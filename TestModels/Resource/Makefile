# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.resources

# TODO-Python-PYTHONPATH: Move into dfyproject.toml
PYTHON_MODULE_NAME=simple_resources

PROJECT_SERVICES := \
	SimpleResources

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

SERVICE_NAMESPACE_SimpleResources=simple.resources

SERVICE_DEPS_SimpleResources :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 


format_net:
	pushd runtimes/net && dotnet format && popd
