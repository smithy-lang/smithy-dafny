# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.boolean

GO_NAMESPACE=simpletypesboolean
PROJECT_SERVICES := \
	SimpleBoolean

MAIN_SERVICE_FOR_RUST := SimpleBoolean

SERVICE_NAMESPACE_SimpleBoolean=simple.types.boolean

SERVICE_DEPS_SimpleBoolean :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleBoolean"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# Python

PYTHON_MODULE_NAME=simple_types_boolean

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesBooleanTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.boolean.internaldafny.types\" } SimpleTypesBooleanTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesBooleanTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.boolean.internaldafny\" } SimpleBoolean refines AbstractSimpleTypesBooleanService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleBoolean refines AbstractSimpleTypesBooleanService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleBooleanImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.boolean.internaldafny.wrapped\"} WrappedSimpleTypesBooleanService refines WrappedAbstractSimpleTypesBooleanService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesBooleanService refines WrappedAbstractSimpleTypesBooleanService {"
