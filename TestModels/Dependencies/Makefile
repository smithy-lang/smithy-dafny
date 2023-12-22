# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PYTHON_MODULE_NAME=simple_dependencies

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
