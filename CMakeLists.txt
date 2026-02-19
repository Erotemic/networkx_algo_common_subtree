cmake_minimum_required(VERSION 3.15)

project(networkx_algo_common_subtree LANGUAGES C CXX)

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

find_package(Python3 COMPONENTS Interpreter Development.Module REQUIRED)

execute_process(
  COMMAND "${Python3_EXECUTABLE}" -c "import sysconfig; print(sysconfig.get_config_var('EXT_SUFFIX') or '')"
  OUTPUT_VARIABLE PYTHON_EXT_SUFFIX
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

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
    message(WARNING "cargo not found; skipping Rust extension build")
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

    add_custom_command(
      OUTPUT "${_rust_ext_path}"
      COMMAND "${CMAKE_COMMAND}" -E env
        PYO3_BUILD_EXTENSION_MODULE=1
        PYO3_PYTHON=${Python3_EXECUTABLE}
        "${CARGO_EXECUTABLE}" build
        --manifest-path "${CMAKE_CURRENT_SOURCE_DIR}/rust/Cargo.toml"
        --target-dir "${_cargo_target_dir}"
        ${_cargo_release_arg}
      COMMAND "${CMAKE_COMMAND}" -E copy_if_different "${_cargo_lib_path}" "${_rust_ext_path}"
      DEPENDS
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/Cargo.toml"
        "${CMAKE_CURRENT_SOURCE_DIR}/rust/src/lib.rs"
      COMMENT "Building Rust extension module with cargo"
      VERBATIM
    )

    add_custom_target(rust_extension ALL DEPENDS "${_rust_ext_path}")
    install(FILES "${_rust_ext_path}" DESTINATION "networkx_algo_common_subtree")
  endif()
endif()
