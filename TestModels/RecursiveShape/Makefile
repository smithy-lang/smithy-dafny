# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
RUST_BENERATED=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleRecursiveShape

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

SERVICE_NAMESPACE_SimpleRecursiveShape=simple.recursiveShape

SERVICE_DEPS_SimpleRecursiveShape :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/RecursiveShape"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

# Python

PYTHON_MODULE_NAME=simple_recursiveShape

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleRecursiveShapeTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.recursiveshape.internaldafny.types\" } SimpleRecursiveShapeTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleRecursiveShapeTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.recursiveshape.internaldafny\"} SimpleRecursiveShape refines AbstractSimpleRecursiveShapeService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleRecursiveShape refines AbstractSimpleRecursiveShapeService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleRecursiveShapeImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.recursiveshape.internaldafny.wrapped\"} WrappedSimpleRecursiveShapeService refines WrappedAbstractSimpleRecursiveShapeService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleRecursiveShapeService refines WrappedAbstractSimpleRecursiveShapeService {"
