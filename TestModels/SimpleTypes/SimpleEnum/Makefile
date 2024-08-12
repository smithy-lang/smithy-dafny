# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyEnum

PROJECT_SERVICES := \
	SimpleEnum

SERVICE_NAMESPACE_SimpleEnum=simple.types.smithyEnum

SERVICE_DEPS_SimpleEnum :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesEnumTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enum.internaldafny.types\" } SimpleTypesEnumTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesEnumTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enum.internaldafny\" } SimpleEnum refines AbstractSimpleTypesEnumService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleEnum refines AbstractSimpleTypesEnumService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleEnumImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enum.internaldafny.wrapped\"} WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesEnumService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesEnumService {"

# Python

PYTHON_MODULE_NAME=simple_types_smithyenum

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr