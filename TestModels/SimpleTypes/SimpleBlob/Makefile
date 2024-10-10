# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=simple.types.blob

PROJECT_SERVICES := \
	SimpleBlob

MAIN_SERVICE_FOR_RUST := SimpleBlob

SERVICE_NAMESPACE_SimpleBlob=simple.types.blob

SERVICE_DEPS_SimpleBlob :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# Python

PYTHON_MODULE_NAME=simple_types_blob

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# This project has no dependencies 
# DEPENDENT-MODELS:=

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleTypesBlobTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.blob.internaldafny.types\" } SimpleTypesBlobTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleTypesBlobTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.blob.internaldafny\" } SimpleBlob refines AbstractSimpleTypesBlobService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleBlob refines AbstractSimpleTypesBlobService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleBlobImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.types.blob.internaldafny.wrapped\"} WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {"
