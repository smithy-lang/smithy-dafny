# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.union

PROJECT_SERVICES := \
	SimpleUnion

SERVICE_NAMESPACE_SimpleUnion=simple.union

SERVICE_DEPS_SimpleUnion :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=simple_union

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

transpile_net_dependencies:
