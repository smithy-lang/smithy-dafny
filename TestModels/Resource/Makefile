# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.resources
# TODO-Python: Move to smithy-build.json once Dafny SmithyBuildPlugin supports language-specific config
PYTHON_MODULE_NAME=simple_resources

PROJECT_SERVICES := \
	SimpleResources

SERVICE_NAMESPACE_SimpleResources=simple.resources

SERVICE_DEPS_SimpleResources :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

format_net:
	pushd runtimes/net && dotnet format && popd
