# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.localService
# TODO-Python: Move to smithy-build.json once Dafny SmithyBuildPlugin supports language-specific config
PYTHON_MODULE_NAME=simple_localservice

PROJECT_SERVICES := \
	SimpleLocalService

SERVICE_NAMESPACE_SimpleLocalService=simple.localService

SERVICE_DEPS_SimpleLocalService :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	# rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	# rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	# rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	# rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
