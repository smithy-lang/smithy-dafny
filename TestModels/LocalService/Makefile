# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1
ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

NAMESPACE=simple.localService

PROJECT_SERVICES := \
	SimpleLocalService

MAIN_SERVICE_FOR_RUST := SimpleLocalService

SERVICE_NAMESPACE_SimpleLocalService=simple.localService

SERVICE_DEPS_SimpleLocalService :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 
GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/LocalService"
# DEPENDENT-MODELS:=

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleLocalServiceTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.localservice.internaldafny.types\" } SimpleLocalServiceTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleLocalServiceTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.localservice.internaldafny\"} SimpleLocalService refines AbstractSimpleLocalServiceService"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleLocalService refines AbstractSimpleLocalServiceService"

WRAPPED_INDEX_FILE_PATH=src/WrappedIndex.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.localservice.internaldafny.wrapped\"} WrappedSimpleLocalService refines WrappedAbstractSimpleLocalServiceService"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleLocalService refines WrappedAbstractSimpleLocalServiceService"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	# rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	# rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	# rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	# rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Python

PYTHON_MODULE_NAME=simple_localservice

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr
