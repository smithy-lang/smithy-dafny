# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleConstraints

SERVICE_NAMESPACE_SimpleConstraints=simple.constraints

SERVICE_DEPS_SimpleConstraints :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

polymorph:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
	make polymorph_dafny DAFNY_VERSION="4.2"
	make polymorph_java DAFNY_VERSION="4.2"
	make polymorph_dotnet DAFNY_VERSION="4.2"
