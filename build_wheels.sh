#!/bin/bash
__doc__="""
SeeAlso:
    pyproject.toml
"""
#pip wheel -w wheelhouse .
# python -m build --wheel -o wheelhouse  #  networkx_algo_common_subtree: +COMMENT_IF(binpy)
cibuildwheel --config-file pyproject.toml --platform linux --arch x86_64  #  networkx_algo_common_subtree: +UNCOMMENT_IF(binpy)
