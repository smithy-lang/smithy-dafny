# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

# DIR_STRUCTURE_V2 is used to signal multiple subprojects/models in one project
DIR_STRUCTURE_V2=V2

PROJECT_SERVICES := \
	DependencyProject \
	PrimaryProject \

MAIN_SERVICE_FOR_RUST := PrimaryProject

SERVICE_NAMESPACE_PrimaryProject=simple.multiplemodels.primaryproject
SERVICE_NAMESPACE_DependencyProject=simple.multiplemodels.dependencyproject

# This project has no dependencies (external to this project)
PROJECT_DEPENDENCIES := 

# Dependencies for each local service
SERVICE_DEPS_DependencyProject := 

SERVICE_DEPS_PrimaryProject := \
	MultipleModels/dafny/DependencyProject \

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/MultipleModels"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=multiple_models

PYTHON_DEPENDENCY_MODULE_NAMES := \
	--dependency-library-name=simple.multiplemodels.dependencyproject=multiple_models

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr

PRIMARY_PROJECT_TYPES_FILE_PATH=dafny/PrimaryProject/Model/SimpleMultiplemodelsPrimaryprojectTypes.dfy
PRIMARY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.primaryproject.internaldafny.types\" } SimpleMultiplemodelsPrimaryprojectTypes"
PRIMARY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleMultiplemodelsPrimaryprojectTypes"

PRIMARY_PROJECT_INDEX_FILE_PATH=dafny/PrimaryProject/src/Index.dfy
PRIMARY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.primaryproject.internaldafny\" } PrimaryProject refines AbstractSimpleMultiplemodelsPrimaryprojectService {"
PRIMARY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING="module PrimaryProject refines AbstractSimpleMultiplemodelsPrimaryprojectService {"

PRIMARY_PROJECT_WRAPPED_INDEX_FILE_PATH=dafny/PrimaryProject/src/WrappedSimpleMultiplemodelsPrimaryprojectImpl.dfy
PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.primaryproject.internaldafny.wrapped\"} WrappedSimpleMultiplemodelsPrimaryprojectService refines WrappedAbstractSimpleMultiplemodelsPrimaryprojectService {"
PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleMultiplemodelsPrimaryprojectService refines WrappedAbstractSimpleMultiplemodelsPrimaryprojectService {"

DEPENDENCY_PROJECT_TYPES_FILE_PATH=dafny/DependencyProject/Model/SimpleMultiplemodelsDependencyprojectTypes.dfy
DEPENDENCY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.dependencyproject.internaldafny.types\" } SimpleMultiplemodelsDependencyprojectTypes"
DEPENDENCY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleMultiplemodelsDependencyprojectTypes"

DEPENDENCY_PROJECT_INDEX_FILE_PATH=dafny/DependencyProject/src/Index.dfy
DEPENDENCY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.dependencyproject.internaldafny\" } DependencyProject refines AbstractSimpleMultiplemodelsDependencyprojectService {"
DEPENDENCY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING="module DependencyProject refines AbstractSimpleMultiplemodelsDependencyprojectService {"

DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_PATH=dafny/DependencyProject/src/WrappedSimpleMultiplemodelsDependencyprojectImpl.dfy
DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.multiplemodels.dependencyproject.internaldafny.wrapped\"} WrappedSimpleMultiplemodelsDependencyprojectService refines WrappedAbstractSimpleMultiplemodelsDependencyprojectService {"
DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleMultiplemodelsDependencyprojectService refines WrappedAbstractSimpleMultiplemodelsDependencyprojectService {"

_sed_types_file_remove_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_TYPES_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_TYPES_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING)

_sed_index_file_remove_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_INDEX_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_INDEX_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING)

_sed_wrapped_types_file_remove_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING)

_sed_types_file_add_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_TYPES_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_TYPES_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_TYPES_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_TYPES_FILE_WITH_EXTERN_STRING)

_sed_index_file_add_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_INDEX_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_INDEX_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_INDEX_FILE_WITH_EXTERN_STRING)

_sed_wrapped_types_file_add_extern:
	$(MAKE) _sed_file SED_FILE_PATH=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(PRIMARY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING)
	$(MAKE) _sed_file SED_FILE_PATH=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(DEPENDENCY_PROJECT_WRAPPED_INDEX_FILE_WITH_EXTERN_STRING)

