# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	CodegenPatches

SERVICE_NAMESPACE_CodegenPatches=simple.codegenpatches

SERVICE_DEPS_CodegenPatches :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/ShubhamChaturvedi7/CodegenPatches"

# This project has no dependencies 
# DEPENDENT-MODELS:= 


clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
