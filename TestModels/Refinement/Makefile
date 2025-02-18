# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
RUST_BENERATED=1

include ../SharedMakefile.mk

NAMESPACE=simple.refinement

PROJECT_SERVICES := \
	SimpleRefinement

MAIN_SERVICE_FOR_RUST := SimpleRefinement

SERVICE_NAMESPACE_SimpleRefinement=simple.refinement

SERVICE_DEPS_SimpleRefinement :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/Refinement"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=simple_refinement

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleRefinementTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.refinement.internaldafny.types\" } SimpleRefinementTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleRefinementTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.refinement.internaldafny\"} SimpleRefinement refines AbstractSimpleRefinementService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleRefinement refines AbstractSimpleRefinementService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleRefinementImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.refinement.internaldafny.wrapped\"} WrappedSimpleRefinementService refines WrappedAbstractSimpleRefinementService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleRefinementService refines WrappedAbstractSimpleRefinementService {"
