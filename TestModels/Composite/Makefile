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
PROJECT_DEPENDENCIES := 

# Dependencies for each local service
SERVICE_DEPS_DependencyProject := 

SERVICE_DEPS_PrimaryProject := \
	Composite/dafny/DependencyProject \

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# DEPENDENT-MODELS:=
# LIBRARIES :=