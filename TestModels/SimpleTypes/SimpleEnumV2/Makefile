# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.enumV2

PROJECT_SERVICES := \
        SimpleTypesEnumV2

MAIN_SERVICE_FOR_RUST := SimpleTypesEnumV2

SERVICE_NAMESPACE_SimpleTypesEnumV2=simple.types.enumV2

SERVICE_DEPS_SimpleTypesEnumV2 :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleEnumV2"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# This project has no dependencies
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=simple_types_smithyenumv2

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesEnumV2Types.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enumv2.internaldafny.types\" } SimpleTypesEnumV2Types"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesEnumV2Types"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enumv2.internaldafny\" } SimpleEnumV2 refines AbstractSimpleTypesEnumV2Service {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleEnumV2 refines AbstractSimpleTypesEnumV2Service {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleEnumImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.enumv2.internaldafny.wrapped\"} WrappedSimpleTypesEnumV2Service refines WrappedAbstractSimpleTypesEnumV2Service {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesEnumV2Service refines WrappedAbstractSimpleTypesEnumV2Service {"
