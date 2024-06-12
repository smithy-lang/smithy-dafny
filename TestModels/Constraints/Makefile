# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleConstraints

SERVICE_NAMESPACE_SimpleConstraints=simple.constraints

SERVICE_DEPS_SimpleConstraints :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/Smithy-dafny/TestModels/Constraints"

PROJECT_DTR := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# First, export DAFNY_VERSION=4.2
# Three separate items, because 'make polymorph_code_gen' doesn't quite work
polymorph:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
	make polymorph_dafny
	make polymorph_java
	make polymorph_dotnet
