#!/usr/bin/env python3
"""Validate release archive metadata, native payloads, sources and SHA256SUMS."""
import argparse
from email.parser import BytesParser
import hashlib
from pathlib import Path
import tarfile
import tomllib
import zipfile

from packaging.utils import canonicalize_name, parse_sdist_filename, parse_wheel_filename
from packaging.requirements import Requirement
from packaging.version import Version


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--tag", default="")
    parser.add_argument("--verify-manifest", action="store_true")
    parser.add_argument("--wheels-only", action="store_true",
                        help="Validate a wheel build job before its separately built sdist is available")
    args = parser.parse_args()
    project = tomllib.loads((Path(__file__).resolve().parents[1] / "pyproject.toml").read_text())["project"]
    expected_name, expected_version = canonicalize_name(project["name"]), Version(project["version"])
    if args.tag:
        assert args.tag == f"v{expected_version}", (args.tag, expected_version)
    files = sorted(p for p in args.directory.iterdir() if p.name.endswith((".whl", ".tar.gz")))
    assert any(p.suffix == ".whl" for p in files), "no wheels"
    if args.wheels_only:
        assert all(p.suffix == ".whl" for p in files), "expected only wheels"
    else:
        assert sum(p.name.endswith(".tar.gz") for p in files) == 1, "expected exactly one sdist"
    checksums = []
    for path in files:
        if path.suffix == ".whl":
            name, version, _, _ = parse_wheel_filename(path.name)
            with zipfile.ZipFile(path) as archive:
                names = archive.namelist()
                meta = [n for n in names if n.endswith(".dist-info/METADATA")]
                assert len(meta) == 1, (path, meta)
                data = archive.read(meta[0])
                assert any(n.startswith("networkx_algo_common_subtree/_rust.") and
                           n.endswith((".so", ".pyd")) for n in names), f"missing fast Rust backend: {path}"
                assert "networkx_algo_common_subtree/unordered.py" in names
        else:
            name, version = parse_sdist_filename(path.name)
            prefix = path.name[:-7] + "/"
            with tarfile.open(path, "r:gz") as archive:
                names = set(archive.getnames())
                assert not any(n.endswith(".enc") or "/submodules/" in n or
                               "/.lake/" in n or "/target/" in n for n in names), \
                    "sdist contains development credentials, submodules or build caches"
                required = ["CMakeLists.txt", "pyproject.toml", "README.rst", "rust/Cargo.toml",
                            "rust/Cargo.lock", "rust/build.rs", "rust/src/graph_bindings.rs",
                            "networkx_algo_common_subtree/unordered.py"]
                required += [f"rust/crates/{crate}/Cargo.toml" for crate in
                             ("verified_ordered_core", "verified_assignment_core", "common_subtree_algorithms")]
                assert all(prefix + n in names for n in required), "sdist missing maintained native/runtime sources"
                data = archive.extractfile(prefix + "PKG-INFO").read()
        assert canonicalize_name(name) == expected_name and version == expected_version, path
        metadata = BytesParser().parsebytes(data)
        assert canonicalize_name(metadata["Name"]) == expected_name, path
        assert Version(metadata["Version"]) == expected_version, path
        assert metadata["Requires-Python"] == project["requires-python"], path
        dependencies = {str(Requirement(r)) for r in metadata.get_all("Requires-Dist", [])}
        assert all(str(Requirement(r)) in dependencies for r in project["dependencies"]), \
            f"distribution dependency metadata differs from pyproject.toml: {path}"
        checksums.append(f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n")
    manifest = args.directory / "SHA256SUMS"
    contents = "".join(checksums)
    if args.verify_manifest:
        assert manifest.read_text() == contents, "distribution checksums changed"
    else:
        manifest.write_text(contents)
    print(f"Validated {len(files)} distributions for {expected_name} {expected_version}; checksums {'verified' if args.verify_manifest else 'written'}.")


if __name__ == "__main__":
    main()
