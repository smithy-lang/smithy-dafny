# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleDependenciesLite

# Dependencies external to this project
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	aws-sdks/kms-lite

PROJECT_INDEX := \
	aws-sdks/kms-lite/src/Index.dfy

SERVICE_NAMESPACE_SimpleDependenciesLite=simple.dependencies.lite

# Dependencies for each local service
SERVICE_DEPS_SimpleDependenciesLite := \
	aws-sdks/kms-lite

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

POLYMORPH_OPTIONS=--generate project-files,client-constructors,impl-stub

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
