# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	CodegenPatches

SERVICE_NAMESPACE_CodegenPatches=simple.codegenpatches

SERVICE_DEPS_CodegenPatches :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=codegen_patches

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleCodegenpatchesTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.codegenpatches.internaldafny.types\" } SimpleCodegenpatchesTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleCodegenpatchesTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.codegenpatches.internaldafny\" } CodegenPatches refines AbstractSimpleCodegenpatchesService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module CodegenPatches refines AbstractSimpleCodegenpatchesService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedCodegenPatchesImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.codegenpatches.internaldafny.wrapped\"} WrappedSimpleCodegenPatchesService refines WrappedAbstractSimpleCodegenpatchesService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleCodegenPatchesService refines WrappedAbstractSimpleCodegenpatchesService {"
