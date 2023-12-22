# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyDouble
# TODO-Python: Move to smithy-build.json once Dafny SmithyBuildPlugin supports language-specific config
PYTHON_MODULE_NAME=simple_types_smithydouble

PROJECT_SERVICES := \
	SimpleDouble

SERVICE_NAMESPACE_SimpleDouble=simple.types.smithyDouble

SERVICE_DEPS_SimpleDouble :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=
transpile_net_dependencies:

format_net:
	pushd runtimes/net && dotnet format && popd
