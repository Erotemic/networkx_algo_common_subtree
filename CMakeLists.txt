cmake_minimum_required(VERSION 3.15)

project(networkx_algo_common_subtree LANGUAGES NONE)

set(_disable_c_extensions "$ENV{DISABLE_C_EXTENSIONS}")
string(TOLOWER "${_disable_c_extensions}" _disable_c_extensions)
if(_disable_c_extensions MATCHES "^(1|on|yes|true)$")
  set(_build_cython_default OFF)
else()
  set(_build_cython_default ON)
endif()

set(_disable_rust_extensions "$ENV{DISABLE_RUST_EXTENSIONS}")
string(TOLOWER "${_disable_rust_extensions}" _disable_rust_extensions)
if(_disable_rust_extensions MATCHES "^(1|on|yes|true)$")
  set(_build_rust_default OFF)
else()
  set(_build_rust_default ON)
endif()

option(BUILD_CYTHON_EXTENSIONS "Build Cython extension modules" ${_build_cython_default})
option(BUILD_RUST_EXTENSIONS "Build Rust extension module" ${_build_rust_default})
option(REQUIRE_RUST_EXTENSIONS "Fail configure if Rust extension cannot be built" OFF)
option(BUILD_LEAN_BACKEND "Build and install the proved exact rational ordered backend" OFF)

if(BUILD_LEAN_BACKEND)
  find_program(LAKE_EXECUTABLE lake REQUIRED)
  set(_lean_executable "${CMAKE_CURRENT_SOURCE_DIR}/proofs/.lake/build/bin/verified_ordered${CMAKE_EXECUTABLE_SUFFIX}")
  file(GLOB_RECURSE _lean_sources CONFIGURE_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/proofs/SubtreeProofs/*.lean")
  add_custom_command(OUTPUT "${_lean_executable}"
    COMMAND "${LAKE_EXECUTABLE}" build verified_ordered
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/proofs"
    DEPENDS ${_lean_sources} "${CMAKE_CURRENT_SOURCE_DIR}/proofs/VerifiedOrderedMain.lean"
      "${CMAKE_CURRENT_SOURCE_DIR}/proofs/lakefile.toml" "${CMAKE_CURRENT_SOURCE_DIR}/proofs/lean-toolchain"
      "${CMAKE_CURRENT_SOURCE_DIR}/proofs/lake-manifest.json"
    VERBATIM)
  add_custom_target(verified_lean_backend ALL DEPENDS "${_lean_executable}")
  install(PROGRAMS "${_lean_executable}" DESTINATION "networkx_algo_common_subtree/_bin")
endif()

set(_cargo_abi_args "")
if(SKBUILD_SABI_COMPONENT)
  if(NOT SKBUILD_SABI_VERSION STREQUAL "3.10")
    message(FATAL_ERROR "Stable ABI builds require wheel.py-api=cp310 and scikit-build-core>=1.0")
  endif()
  if(BUILD_CYTHON_EXTENSIONS)
    message(FATAL_ERROR "Stable ABI wheels require BUILD_CYTHON_EXTENSIONS=OFF; the Cython targets use the version-specific API")
  endif()
  if(NOT BUILD_RUST_EXTENSIONS)
    message(FATAL_ERROR "Stable ABI wheels require BUILD_RUST_EXTENSIONS=ON")
  endif()
  set(REQUIRE_RUST_EXTENSIONS ON)
  set(_cargo_abi_args --features abi3)
endif()

# Rust owns its Python ABI/link configuration through PyO3. Headers and CMake's
# Development.Module target are needed only for the Cython targets.
if(BUILD_CYTHON_EXTENSIONS)
  enable_language(C CXX)
  find_package(Python3 COMPONENTS Interpreter Development.Module REQUIRED)
else()
  find_package(Python3 COMPONENTS Interpreter REQUIRED)
endif()

execute_process(
  COMMAND "${Python3_EXECUTABLE}" -c "import sysconfig; print(sysconfig.get_config_var('EXT_SUFFIX') or '')"
  OUTPUT_VARIABLE PYTHON_EXT_SUFFIX
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
if(SKBUILD_SABI_COMPONENT)
  if(WIN32)
    set(PYTHON_EXT_SUFFIX ".pyd")
  else()
    set(PYTHON_EXT_SUFFIX ".abi3.so")
  endif()
endif()

function(cpu_cython_module cython_source module_name)
  set(_generated_cpp "${CMAKE_CURRENT_BINARY_DIR}/${module_name}.cpp")
  add_custom_command(
    OUTPUT "${_generated_cpp}"
    COMMAND "${Python3_EXECUTABLE}" -m cython --cplus "${CMAKE_CURRENT_SOURCE_DIR}/${cython_source}" -o "${_generated_cpp}"
    DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/${cython_source}"
    COMMENT "Cythonizing ${cython_source}"
    VERBATIM
  )

  Python3_add_library(${module_name} MODULE WITH_SOABI "${_generated_cpp}")
  set_target_properties(${module_name} PROPERTIES PREFIX "")
  target_include_directories(${module_name} PRIVATE "${Python3_INCLUDE_DIRS}")
  target_compile_definitions(${module_name} PUBLIC "NPY_NO_DEPRECATED_API")

  install(TARGETS ${module_name}
    LIBRARY DESTINATION "networkx_algo_common_subtree"
    RUNTIME DESTINATION "networkx_algo_common_subtree"
  )
endfunction()

if(BUILD_CYTHON_EXTENSIONS)
  add_subdirectory("networkx_algo_common_subtree")
endif()

if(BUILD_RUST_EXTENSIONS)
  find_program(CARGO_EXECUTABLE cargo)
  if(NOT CARGO_EXECUTABLE)
    if(REQUIRE_RUST_EXTENSIONS)
    message(FATAL_ERROR "cargo not found but REQUIRE_RUST_EXTENSIONS=ON")
  else()
    message(WARNING "cargo not found; skipping Rust extension build")
  endif()
  else()
    if(CMAKE_BUILD_TYPE STREQUAL "Debug")
      set(_cargo_profile_dir "debug")
      set(_cargo_release_arg "")
    else()
      set(_cargo_profile_dir "release")
      set(_cargo_release_arg "--release")
    endif()

    set(_cargo_target_dir "${CMAKE_CURRENT_BINARY_DIR}/cargo-target")
    if(WIN32)
      set(_cargo_lib_name "_rust.dll")
    elseif(APPLE)
      set(_cargo_lib_name "lib_rust.dylib")
    else()
      set(_cargo_lib_name "lib_rust.so")
    endif()

    set(_cargo_lib_path "${_cargo_target_dir}/${_cargo_profile_dir}/${_cargo_lib_name}")
    set(_rust_ext_path "${CMAKE_CURRENT_BINARY_DIR}/_rust${PYTHON_EXT_SUFFIX}")

    file(GLOB_RECURSE _rust_sources CONFIGURE_DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/src/*.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/verified_ordered_core/src/*.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/verified_assignment_core/src/*.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/common_subtree_algorithms/src/*.rs")

    add_custom_command(
      OUTPUT "${_rust_ext_path}"
      COMMAND "${CMAKE_COMMAND}" -E env
        PYO3_BUILD_EXTENSION_MODULE=1
        PYO3_PYTHON=${Python3_EXECUTABLE}
        "${CARGO_EXECUTABLE}" build
        --manifest-path "${CMAKE_CURRENT_SOURCE_DIR}/rust/Cargo.toml"
        --target-dir "${_cargo_target_dir}"
        --locked
        ${_cargo_release_arg}
        ${_cargo_abi_args}
      COMMAND "${CMAKE_COMMAND}" -E copy_if_different "${_cargo_lib_path}" "${_rust_ext_path}"
      DEPENDS
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/Cargo.toml"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/src/lib.rs"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/build.rs"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/Cargo.lock"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/verified_ordered_core/Cargo.toml"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/verified_assignment_core/Cargo.toml"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/crates/common_subtree_algorithms/Cargo.toml"
        ${_rust_sources}
      COMMENT "Building Rust extension module with cargo"
      VERBATIM
    )

    add_custom_target(rust_extension ALL DEPENDS "${_rust_ext_path}")
    install(FILES "${_rust_ext_path}" DESTINATION "networkx_algo_common_subtree")
  endif()
endif()
