#!/usr/bin/env python
# Generated by ~/code/xcookie/xcookie/builders/setup.py
# based on part ~/code/xcookie/xcookie/rc/setup.py.in
import sys
import re
from os.path import exists, dirname, join
from setuptools import find_packages

if exists("CMakeLists.txt"):
    try:
        import os

        # Hack to disable all compiled extensions
        val = os.environ.get("DISABLE_C_EXTENSIONS", "").lower()
        use_setuptools = val in {"true", "on", "yes", "1"}

    except ImportError:
        use_setuptools = True
else:
    use_setuptools = True

if not use_setuptools:
    try:
        from skbuild import setup as skb_setup

        setup = skb_setup  # NOQA
    except Exception:
        use_setuptools = True
        import warnings

        warnings.warn("scikit-build was not found, but is required to build binaries")

if use_setuptools:
    from setuptools import setup


def parse_version(fpath):
    """
    Statically parse the version number from a python file
    """
    value = static_parse("__version__", fpath)
    return value


def static_parse(varname, fpath):
    """
    Statically parse the a constant variable from a python file
    """
    import ast

    if not exists(fpath):
        raise ValueError("fpath={!r} does not exist".format(fpath))
    with open(fpath, "r") as file_:
        sourcecode = file_.read()
    pt = ast.parse(sourcecode)

    class StaticVisitor(ast.NodeVisitor):
        def visit_Assign(self, node):
            for target in node.targets:
                if getattr(target, "id", None) == varname:
                    try:
                        self.static_value = node.value.value
                    except AttributeError:
                        self.static_value = node.value.s

    visitor = StaticVisitor()
    visitor.visit(pt)
    try:
        value = visitor.static_value
    except AttributeError:
        import warnings

        value = "Unknown {}".format(varname)
        warnings.warn(value)
    return value


def parse_description():
    """
    Parse the description in the README file

    CommandLine:
        pandoc --from=markdown --to=rst --output=README.rst README.md
        python -c "import setup; print(setup.parse_description())"
    """
    readme_fpath = join(dirname(__file__), "README.rst")
    # This breaks on pip install, so check that it exists.
    if exists(readme_fpath):
        with open(readme_fpath, "r") as f:
            text = f.read()
        return text
    return ""


def parse_requirements(fname="requirements.txt", versions=False):
    """
    Parse the package dependencies listed in a requirements file but strips
    specific versioning information.

    Args:
        fname (str): path to requirements file
        versions (bool | str):
            If true include version specs.
            If strict, then pin to the minimum version.

    Returns:
        List[str]: list of requirements items

    CommandLine:
        python -c "import setup, ubelt; print(ubelt.urepr(setup.parse_requirements()))"
    """
    require_fpath = fname

    def parse_line(line, dpath=""):
        """
        Parse information from a line in a requirements text file

        line = 'git+https://a.com/somedep@sometag#egg=SomeDep'
        line = '-e git+https://a.com/somedep@sometag#egg=SomeDep'
        """
        # Remove inline comments
        comment_pos = line.find(" #")
        if comment_pos > -1:
            line = line[:comment_pos]

        if line.startswith("-r "):
            # Allow specifying requirements in other files
            target = join(dpath, line.split(" ")[1])
            for info in parse_require_file(target):
                yield info
        else:
            # See: https://www.python.org/dev/peps/pep-0508/
            info = {"line": line}
            if line.startswith("-e "):
                info["package"] = line.split("#egg=")[1]
            else:
                if "--find-links" in line:
                    # setuptools does not seem to handle find links
                    line = line.split("--find-links")[0]
                if ";" in line:
                    pkgpart, platpart = line.split(";")
                    # Handle platform specific dependencies
                    # setuptools.readthedocs.io/en/latest/setuptools.html
                    # #declaring-platform-specific-dependencies
                    plat_deps = platpart.strip()
                    info["platform_deps"] = plat_deps
                else:
                    pkgpart = line
                    platpart = None

                # Remove versioning from the package
                pat = "(" + "|".join([">=", "==", ">"]) + ")"
                parts = re.split(pat, pkgpart, maxsplit=1)
                parts = [p.strip() for p in parts]

                info["package"] = parts[0]
                if len(parts) > 1:
                    op, rest = parts[1:]
                    version = rest  # NOQA
                    info["version"] = (op, version)
            yield info

    def parse_require_file(fpath):
        dpath = dirname(fpath)
        with open(fpath, "r") as f:
            for line in f.readlines():
                line = line.strip()
                if line and not line.startswith("#"):
                    for info in parse_line(line, dpath=dpath):
                        yield info

    def gen_packages_items():
        if exists(require_fpath):
            for info in parse_require_file(require_fpath):
                parts = [info["package"]]
                if versions and "version" in info:
                    if versions == "strict":
                        # In strict mode, we pin to the minimum version
                        if info["version"]:
                            # Only replace the first >= instance
                            verstr = "".join(info["version"]).replace(">=", "==", 1)
                            parts.append(verstr)
                    else:
                        parts.extend(info["version"])
                if not sys.version.startswith("3.4"):
                    # apparently package_deps are broken in 3.4
                    plat_deps = info.get("platform_deps")
                    if plat_deps is not None:
                        parts.append(";" + plat_deps)
                item = "".join(parts)
                if item:
                    yield item

    packages = list(gen_packages_items())
    return packages


# # Maybe use in the future? But has private deps
# def parse_requirements_alt(fpath='requirements.txt', versions='loose'):
#     """
#     Args:
#         versions (str): can be
#             False or "free" - remove all constraints
#             True or "loose" - use the greater or equal (>=) in the req file
#             strict - replace all greater equal with equals
#     """
#     # Note: different versions of pip might have different internals.
#     # This may need to be fixed.
#     from pip._internal.req import parse_requirements
#     from pip._internal.network.session import PipSession
#     requirements = []
#     for req in parse_requirements(fpath, session=PipSession()):
#         if not versions or versions == 'free':
#             req_name = req.requirement.split(' ')[0]
#             requirements.append(req_name)
#         elif versions == 'loose' or versions is True:
#             requirements.append(req.requirement)
#         elif versions == 'strict':
#             part1, *rest = req.requirement.split(';')
#             strict_req = ';'.join([part1.replace('>=', '==')] + rest)
#             requirements.append(strict_req)
#         else:
#             raise KeyError(versions)
#     requirements = [r.replace(' ', '') for r in requirements]
#     return requirements


NAME = "networkx_algo_common_subtree"
INIT_PATH = "networkx_algo_common_subtree/__init__.py"
VERSION = parse_version(INIT_PATH)
if __name__ == "__main__":
    setupkw = {}

    setupkw["install_requires"] = parse_requirements(
        "requirements/runtime.txt", versions="loose"
    )
    setupkw["extras_require"] = {
        "all": parse_requirements("requirements.txt", versions="loose"),
        "runtime": parse_requirements("requirements/runtime.txt", versions="loose"),
        "tests": parse_requirements("requirements/tests.txt", versions="loose"),
        "optional": parse_requirements("requirements/optional.txt", versions="loose"),
        "build": parse_requirements("requirements/build.txt", versions="loose"),
        "docs": parse_requirements("requirements/docs.txt", versions="loose"),
        "all-strict": parse_requirements("requirements.txt", versions="strict"),
        "runtime-strict": parse_requirements(
            "requirements/runtime.txt", versions="strict"
        ),
        "tests-strict": parse_requirements("requirements/tests.txt", versions="strict"),
        "optional-strict": parse_requirements(
            "requirements/optional.txt", versions="strict"
        ),
        "build-strict": parse_requirements("requirements/build.txt", versions="strict"),
        "docs-strict": parse_requirements("requirements/docs.txt", versions="strict"),
    }
    setupkw["name"] = NAME
    setupkw["version"] = VERSION
    setupkw["author"] = "Jon Crall"
    setupkw["author_email"] = "erotemic@gmail.com"
    setupkw["url"] = "https://github.com/Erotemic/networkx_algo_common_subtree"
    setupkw["description"] = (
        "A networkx implementation of algorithms to find common ordered subtree minors and isomorphisms"
    )
    setupkw["long_description"] = parse_description()
    setupkw["long_description_content_type"] = "text/x-rst"
    setupkw["license"] = "Apache 2"
    setupkw["packages"] = find_packages(".")
    setupkw["python_requires"] = ">=3.8"
    setupkw["classifiers"] = [
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "Topic :: Utilities",
        "License :: OSI Approved :: Apache Software License",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
    ]
    setupkw["package_data"] = {"": ["requirements/*.txt"]}
    setup(**setupkw)
