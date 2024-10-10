# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyEnum

PROJECT_SERVICES := \
	SimpleEnum

MAIN_SERVICE_FOR_RUST := SimpleEnum

SERVICE_NAMESPACE_SimpleEnum=simple.types.smithyEnum

SERVICE_DEPS_SimpleEnum :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=simple_types_smithyenum

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesSmithyEnumTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithyenum.internaldafny.types\" } SimpleTypesSmithyEnumTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesSmithyEnumTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithyenum.internaldafny\" } SimpleEnum refines AbstractSimpleTypesSmithyEnumService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleEnum refines AbstractSimpleTypesSmithyEnumService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleEnumImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.smithyenum.internaldafny.wrapped\"} WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesSmithyEnumService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesSmithyEnumService {"
