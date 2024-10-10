# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

NAMESPACE=simple.positional

PROJECT_SERVICES := \
	SimplePositional

MAIN_SERVICE_FOR_RUST := SimplePositional

SERVICE_NAMESPACE_SimplePositional=simple.positional

SERVICE_DEPS_SimplePositional :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

POLYMORPH_OPTIONS=--generate project-files,client-constructors

# Python

PYTHON_MODULE_NAME=simple_positional

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimplePositionalTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.positional.internaldafny.types\" } SimplePositionalTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimplePositionalTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.positional.internaldafny\" } SimplePositional refines AbstractSimplePositionalService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimplePositional refines AbstractSimplePositionalService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimplePositionalImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:options \"--function-syntax:4\"} {:extern \"simple.positional.internaldafny.wrapped\"} WrappedSimplePositionalService refines WrappedAbstractSimplePositionalService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module {:options \"--function-syntax:4\"} WrappedSimplePositionalService refines WrappedAbstractSimplePositionalService {"
