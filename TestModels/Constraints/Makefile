# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleConstraints

SERVICE_NAMESPACE_SimpleConstraints=simple.constraints

NAMESPACE=simple.constraints

MAIN_SERVICE_FOR_RUST := SimpleConstraints

SERVICE_DEPS_SimpleConstraints :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Patch out tests that Rust codegen doesn't support
transpile_rust: | transpile_implementation_rust transpile_dependencies_rust remove_unsupported_rust_tests

remove_unsupported_rust_tests:
	$(MAKE) _sed_file \
		SED_FILE_PATH=$(LIBRARY_ROOT)/runtimes/rust/src/implementation_from_dafny.rs \
		SED_BEFORE_STRING='let mut allowBadUtf8BytesFromDafny: bool = true' \
		SED_AFTER_STRING='let mut allowBadUtf8BytesFromDafny: bool = false'

# Python

PYTHON_MODULE_NAME=simple_constraints

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleConstraintsTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny.types\" } SimpleConstraintsTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleConstraintsTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny\" } SimpleConstraints refines AbstractSimpleConstraintsService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleConstraints refines AbstractSimpleConstraintsService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleConstraintsImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny.wrapped\"} WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {"
