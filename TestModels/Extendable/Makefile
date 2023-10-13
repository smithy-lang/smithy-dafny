# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.extendable.resources
# TODO: Move to smithy-build.json once Dafny plugin supports language-specific config
PYTHON_MODULE_NAME=simple_extendable_resources

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

format_net:
	pushd runtimes/net && dotnet format && popd

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
