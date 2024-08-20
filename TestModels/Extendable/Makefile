# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

NAMESPACE=simple.extendable.resources

PROJECT_SERVICES := \
	SimpleExtendableResources

SERVICE_NAMESPACE_SimpleExtendableResources=simple.extendable.resources

SERVICE_DEPS_SimpleExtendableResources :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 


format_net:
	pushd runtimes/net && dotnet format && popd

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
