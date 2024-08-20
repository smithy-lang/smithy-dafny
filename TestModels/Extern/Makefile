# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleExtern

SERVICE_NAMESPACE_SimpleExtern=simple.dafnyExtern

SERVICE_DEPS_SimpleExtern :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

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
