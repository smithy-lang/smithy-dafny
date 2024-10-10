# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyLong

PROJECT_SERVICES := \
	SimpleLong

MAIN_SERVICE_FOR_RUST := SimpleLong

SERVICE_NAMESPACE_SimpleLong=simple.types.smithyLong

SERVICE_DEPS_SimpleLong :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=simple_types_smithylong

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesSmithyLongTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithylong.internaldafny.types\" } SimpleTypesSmithyLongTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesSmithyLongTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithylong.internaldafny\" } SimpleLong refines AbstractSimpleTypesSmithyLongService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleLong refines AbstractSimpleTypesSmithyLongService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleLongImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithylong.internaldafny.wrapped\"} WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesSmithyLongService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesSmithyLongService {"
