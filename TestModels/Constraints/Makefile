# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleConstraints

SERVICE_NAMESPACE_SimpleConstraints=simple.constraints

SERVICE_DEPS_SimpleConstraints :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# First, export DAFNY_VERSION=4.2
# Three separate items, because 'make polymorph_code_gen' doesn't quite work
polymorph:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
	make polymorph_dafny
	make polymorph_java
	make polymorph_dotnet

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleConstraintsTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny.types\" } SimpleConstraintsTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleConstraintsTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny\" } SimpleConstraints refines AbstractSimpleConstraintsService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleConstraints refines AbstractSimpleConstraintsService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleConstraintsImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.constraints.internaldafny.wrapped\"} WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {"
