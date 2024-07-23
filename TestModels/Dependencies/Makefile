# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleDependencies

# Dependencies external to this project
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	Resource \
	Errors \
	Extendable \
	Constraints

PROJECT_INDEX := \
	Resource/src/Index.dfy \
	Errors/src/Index.dfy \
	Extendable/src/Index.dfy \
	Constraints/src/Index.dfy

SERVICE_NAMESPACE_SimpleDependencies=simple.dependencies

# Dependencies for each local service
SERVICE_DEPS_SimpleDependencies := \
	Resource \
	Errors \
	Extendable \
	Constraints

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Python

PYTHON_MODULE_NAME=simple_dependencies

PYTHON_DEPENDENCY_MODULE_NAMES := \
	--dependency-library-name=simple.resources=simple_resources \
	--dependency-library-name=simple.errors=simple_errors \
	--dependency-library-name=simple.extendable.resources=simple_extendable_resources \
	--dependency-library-name=simple.constraints=simple_constraints

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../Resource/runtimes/python/src/simple_resources/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../Errors/runtimes/python/src/simple_errors/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../Extendable/runtimes/python/src/simple_extendable_resources/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../Constraints/runtimes/python/src/simple_constraints/internaldafny/generated/dafny_src-py.dtr
