# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

TRANSPILE_TESTS_IN_RUST=1

RUST_OTHER_FILES := runtimes/rust/src/factory.rs

include ../SharedMakefile.mk

NAMESPACE=simple.extendable.resources

PROJECT_SERVICES := \
	SimpleExtendableResources

MAIN_SERVICE_FOR_RUST := SimpleExtendableResources

SERVICE_NAMESPACE_SimpleExtendableResources=simple.extendable.resources

SERVICE_DEPS_SimpleExtendableResources :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/Extendable"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr


# This project has no dependencies 
# DEPENDENT-MODELS:= 


format_net:
	pushd runtimes/net && dotnet format && popd

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Python

PYTHON_MODULE_NAME=simple_extendable_resources

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleExtendableResourcesTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.extendable.resources.internaldafny.types\" } SimpleExtendableResourcesTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleExtendableResourcesTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.extendable.resources.internaldafny\"} SimpleExtendableResources refines AbstractSimpleExtendableResourcesService"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleExtendableResources refines AbstractSimpleExtendableResourcesService"

WRAPPED_INDEX_FILE_PATH=src/WrappedIndex.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.extendable.resources.internaldafny.wrapped\"} WrappedSimpleExtendableResources refines WrappedAbstractSimpleExtendableResourcesService"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleExtendableResources refines WrappedAbstractSimpleExtendableResourcesService"

EXTERN_NATIVE_RESOURCE_FACTORY_FILE_PATH=test/NativeResourceFactory.dfy
EXTERN_NATIVE_RESOURCE_FACTORY_WITH_EXTERN_STRING="module {:extern \"simple.extendable.resources.internaldafny.nativeresourcefactory\"} NativeResourceFactory"
EXTERN_NATIVE_RESOURCE_FACTORY_WITHOUT_EXTERN_STRING="module {:extern} NativeResourceFactory"

_sed_index_file_remove_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(EXTERN_NATIVE_RESOURCE_FACTORY_FILE_PATH) SED_BEFORE_STRING=$(EXTERN_NATIVE_RESOURCE_FACTORY_WITH_EXTERN_STRING) SED_AFTER_STRING=$(EXTERN_NATIVE_RESOURCE_FACTORY_WITHOUT_EXTERN_STRING)

_sed_index_file_add_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITH_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(EXTERN_NATIVE_RESOURCE_FACTORY_FILE_PATH) SED_BEFORE_STRING=$(EXTERN_NATIVE_RESOURCE_FACTORY_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(EXTERN_NATIVE_RESOURCE_FACTORY_WITH_EXTERN_STRING)
