# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.union

PROJECT_SERVICES := \
	SimpleUnion

SERVICE_NAMESPACE_SimpleUnion=simple.union

SERVICE_DEPS_SimpleUnion :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

PROJECT_DTR := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

GO_MODULE_NAME="github.com/Smithy-dafny/TestModels/Union"

# This project has no dependencies
# DEPENDENT-MODELS:=

transpile_net_dependencies:
