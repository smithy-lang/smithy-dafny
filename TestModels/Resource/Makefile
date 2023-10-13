# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.resources
# TODO: Move to smithy-build.json once Dafny plugin supports language-specific config
PYTHON_MODULE_NAME=simple_resources

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

format_net:
	pushd runtimes/net && dotnet format && popd
