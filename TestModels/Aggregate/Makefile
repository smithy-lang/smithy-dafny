# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleAggregate

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

SERVICE_NAMESPACE_SimpleAggregate=simple.aggregate

SERVICE_DEPS_SimpleAggregate :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

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

# Python

PYTHON_MODULE_NAME=simple_aggregate

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr