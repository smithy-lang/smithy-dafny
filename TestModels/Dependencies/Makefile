# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleDependencies

# Dependencies external to this project
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	Resource \
	Errors \
	Extendable \
	Constraints

PROJECT_INDEX := \
	Resource/src/Index.dfy \
	Errors/src/Index.dfy \
	Extendable/src/Index.dfy \
	Constraints/src/Index.dfy

PROJECT_DTR := \
	Resource/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
	Errors/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
	Extendable/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
	Constraints/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr

SERVICE_NAMESPACE_SimpleDependencies=simple.dependencies

# Dependencies for each local service
SERVICE_DEPS_SimpleDependencies := \
	Resource \
	Errors \
	Extendable \
	Constraints

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

GO_MODULE_NAME="github.com/Smithy-dafny/TestModels/Dependencies"

GO_DEPENDENCY_MODULE_NAMES := \
	--dependency-module-name=simple.constraints=github.com/Smithy-dafny/TestModels/Constraints \
	--dependency-module-name=simple.errors=github.com/Smithy-dafny/TestModels/Errors \
	--dependency-module-name=simple.extendable.resources=github.com/Smithy-dafny/TestModels/Extendable \
	--dependency-module-name=simple.resources=github.com/Smithy-dafny/TestModels/Resource


clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
