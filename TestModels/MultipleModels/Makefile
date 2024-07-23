# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

# DIR_STRUCTURE_V2 is used to signal multiple subprojects/models in one project
DIR_STRUCTURE_V2=V2

PROJECT_SERVICES := \
	DependencyProject \
	PrimaryProject \

SERVICE_NAMESPACE_PrimaryProject=simple.multiplemodels.primaryproject
SERVICE_NAMESPACE_DependencyProject=simple.multiplemodels.dependencyproject

# This project has no dependencies (external to this project)
PROJECT_DEPENDENCIES := 

# Dependencies for each local service
SERVICE_DEPS_DependencyProject := 

SERVICE_DEPS_PrimaryProject := \
	MultipleModels/dafny/DependencyProject \

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=multiple_models

PYTHON_DEPENDENCY_MODULE_NAMES := \
	--dependency-library-name=simple.multiplemodels.dependencyproject=multiple_models

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr