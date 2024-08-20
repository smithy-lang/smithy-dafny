# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.integer

PROJECT_SERVICES := \
	SimpleInteger

SERVICE_NAMESPACE_SimpleInteger=simple.types.integer

SERVICE_DEPS_SimpleInteger :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=

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
