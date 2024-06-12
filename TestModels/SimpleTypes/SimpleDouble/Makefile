# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyDouble

PROJECT_SERVICES := \
	SimpleDouble

SERVICE_NAMESPACE_SimpleDouble=simple.types.smithyDouble

SERVICE_DEPS_SimpleDouble :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/Smithy-dafny/TestModels/SimpleTypes/SimpleDouble"

PROJECT_DTR := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# This project has no dependencies 
# DEPENDENT-MODELS:= 

transpile_net_dependencies:

format_net:
	pushd runtimes/net && dotnet format && popd
