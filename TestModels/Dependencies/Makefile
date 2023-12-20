# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleDependencies

SERVICE_NAMESPACE_SimpleDependencies=simple.dependencies

SERVICE_DEPS_SimpleDependencies := \
	Resource \
	Errors \
	Extendable \
	Constraints \

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project takes dependencies on:
# - SimpleResource
# - SimpleErrors
# - SimpleExtendableResource
# - and SimpleConstraints modules.
# DEPENDENT-MODELS:= \
# 	Resource \
# 	Errors \
# 	Extendable \
# 	Constraints
# LIBRARIES := Resource \
# 	Errors \
# 	Extendable \
# 	Constraints

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
