# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

NAMESPACE=simple.union

PROJECT_SERVICES := \
	SimpleUnion

MAIN_SERVICE_FOR_RUST := SimpleUnion

SERVICE_NAMESPACE_SimpleUnion=simple.union

SERVICE_DEPS_SimpleUnion :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=simple_union

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

transpile_net_dependencies:

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleUnionTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.union.internaldafny.types\" } SimpleUnionTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleUnionTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.union.internaldafny\" } SimpleUnion refines AbstractSimpleUnionService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleUnion refines AbstractSimpleUnionService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleUnionImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.union.internaldafny.wrapped\"} WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {"
