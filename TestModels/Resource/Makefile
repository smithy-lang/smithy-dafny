# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.resources
DAFNY_VERSION=--dafny-version 4.3

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

format_net:
	pushd runtimes/net && dotnet format && popd
