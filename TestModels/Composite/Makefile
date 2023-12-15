# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

DIR_STRUCTURE_V2=V2

PROJECT_SERVICES := \
	PrimaryProject \
	DependencyProject \

SERVICE_NAMESPACE_PrimaryProject=simple.composite.primaryproject
SERVICE_NAMESPACE_DependencyProject=simple.composite.dependencyproject

# This project has no dependencies (external to this project)
# Dependencies for each local service
SERVICE_DEPS_DependencyProject := \
	Composite/dafny/PrimaryProject \

SERVICE_DEPS_PrimaryProject := \
	Composite/dafny/DependencyProject \

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# DEPENDENT-MODELS:=
# LIBRARIES :=

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
