# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleExtern

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

SERVICE_NAMESPACE_SimpleExtern=simple.dafnyExtern

SERVICE_DEPS_SimpleExtern :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/Extern"
# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=simple_dafnyextern

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleDafnyExternTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.dafnyextern.internaldafny.types\" } SimpleDafnyExternTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleDafnyExternTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.dafnyextern.internaldafny\" } SimpleExtern refines AbstractSimpleDafnyExternService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleExtern refines AbstractSimpleDafnyExternService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleExternImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.dafnyextern.internaldafny.wrapped\"} WrappedSimpleExternService refines WrappedAbstractSimpleDafnyExternService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleExternService refines WrappedAbstractSimpleDafnyExternService {"
