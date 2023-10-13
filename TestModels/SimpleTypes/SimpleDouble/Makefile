# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyDouble
# TODO: Move to smithy-build.json once Dafny plugin supports language-specific config
PYTHON_MODULE_NAME=simple_types_smithydouble

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=
transpile_net_dependencies:

format_net:
	pushd runtimes/net && dotnet format && popd
