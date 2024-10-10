# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.integer

PROJECT_SERVICES := \
	SimpleInteger

MAIN_SERVICE_FOR_RUST := SimpleInteger

SERVICE_NAMESPACE_SimpleInteger=simple.types.integer

SERVICE_DEPS_SimpleInteger :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=simple_types_integer

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesIntegerTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.integer.internaldafny.types\" } SimpleTypesIntegerTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesIntegerTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.integer.internaldafny\" } SimpleInteger refines AbstractSimpleTypesIntegerService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleInteger refines AbstractSimpleTypesIntegerService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleIntegerImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.integer.internaldafny.wrapped\"} WrappedSimpleTypesIntegerService refines WrappedAbstractSimpleTypesIntegerService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesIntegerService refines WrappedAbstractSimpleTypesIntegerService {"
