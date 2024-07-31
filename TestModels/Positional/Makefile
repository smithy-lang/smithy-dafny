# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.positional

PROJECT_SERVICES := \
	SimplePositional

SERVICE_NAMESPACE_SimplePositional=simple.positional

SERVICE_DEPS_SimplePositional :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/Smithy-dafny/TestModels/Positional"

PROJECT_DTR := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
	
# This project has no dependencies 
# DEPENDENT-MODELS:= 

POLYMORPH_OPTIONS=--generate project-files,client-constructors

