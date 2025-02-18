# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

NAMESPACE=simple.orphaned

PROJECT_SERVICES := \
	SimpleOrphaned

MAIN_SERVICE_FOR_RUST := SimpleOrphaned

SERVICE_NAMESPACE_SimpleOrphaned=simple.orphaned

SERVICE_DEPS_SimpleOrphaned :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

POLYMORPH_OPTIONS=--generate project-files,client-constructors\

# Go

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/OrphanedShapes"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

# Python

PYTHON_MODULE_NAME=simple_orphaned

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleOrphanedTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.orphaned.internaldafny.types\" } SimpleOrphanedTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleOrphanedTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.orphaned.internaldafny\" } SimpleOrphaned refines AbstractSimpleOrphanedService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleOrphaned refines AbstractSimpleOrphanedService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleOrphanedImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:options \"--function-syntax:4\"} {:extern \"simple.orphaned.internaldafny.wrapped\"} WrappedSimpleOrphanedService refines WrappedAbstractSimpleOrphanedService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module {:options \"--function-syntax:4\"} WrappedSimpleOrphanedService refines WrappedAbstractSimpleOrphanedService {"
