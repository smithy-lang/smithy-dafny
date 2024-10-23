# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleErrors

MAIN_SERVICE_FOR_RUST := SimpleErrors

SERVICE_NAMESPACE_SimpleErrors=simple.errors

SERVICE_DEPS_SimpleErrors :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/Errors"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

# This project has no dependencies 
# DEPENDENT-MODELS:= 

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Python

PYTHON_MODULE_NAME=simple_errors

TRANSLATION_RECORD_PYTHON := \
	--translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleErrorsTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.errors.internaldafny.types\" } SimpleErrorsTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleErrorsTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.errors.internaldafny\" } SimpleErrors refines AbstractSimpleErrorsService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleErrors refines AbstractSimpleErrorsService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleErrorsImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.errors.internaldafny.wrapped\"} WrappedSimpleErrorsService refines WrappedAbstractSimpleErrorsService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleErrorsService refines WrappedAbstractSimpleErrorsService {"
