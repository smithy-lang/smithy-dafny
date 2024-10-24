# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleDocumentation

MAIN_SERVICE_FOR_RUST := SimpleDocumentation

SERVICE_NAMESPACE_SimpleDocumentation=simple.documentation

SERVICE_DEPS_SimpleDocumentation :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

POLYMORPH_OPTIONS=--generate client-constructors,project-files

# Python

PYTHON_MODULE_NAME=simple_documentation

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleDocumentationTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.documentation.internaldafny.types\" } SimpleDocumentationTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleDocumentationTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.documentation.internaldafny\" } SimpleDocumentation refines AbstractSimpleDocumentationService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleDocumentation refines AbstractSimpleDocumentationService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleDocumentationImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:options \"--function-syntax:4\"} {:extern \"simple.documentation.internaldafny.wrapped\"} WrappedSimpleDocumentationService refines WrappedAbstractSimpleDocumentationService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module {:options \"--function-syntax:4\"} WrappedSimpleDocumentationService refines WrappedAbstractSimpleDocumentationService {"
