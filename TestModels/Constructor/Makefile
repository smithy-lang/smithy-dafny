# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

NAMESPACE=simple.constructor

PROJECT_SERVICES := \
	SimpleConstructor

MAIN_SERVICE_FOR_RUST := SimpleConstructor

SERVICE_NAMESPACE_SimpleConstructor=simple.constructor

SERVICE_DEPS_SimpleConstructor :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=simple_constructor

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleConstructorTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constructor.internaldafny.types\" } SimpleConstructorTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleConstructorTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constructor.internaldafny\" } SimpleConstructor refines AbstractSimpleConstructorService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleConstructor refines AbstractSimpleConstructorService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleConstructorImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constructor.internaldafny.wrapped\"} WrappedSimpleConstructorService refines WrappedAbstractSimpleConstructorService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleConstructorService refines WrappedAbstractSimpleConstructorService {"
