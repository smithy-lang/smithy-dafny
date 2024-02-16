# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These make targets that are shared
# between all the Dafny projects
# in this repo.
# They will only function if executed inside a project directory.

# There are serveral variables that are used here.
# The expectation is to define these variables
# inside each project.

# Variables:
# MAX_RESOURCE_COUNT -- The Dafny report generator max resource count.
# 	This is is per project because the verification variability can differ.
# LIBRARIES -- List of dependencies for the project.
# 	It should be the list of top leve directory names
# SMITHY_NAMESPACE -- The smithy namespace to use for code generation. 
# AWS_SDK_CMD -- the `--aws-sdk` command to generate AWS SDK style interfaces

# This evaluates to the local path _of this file_.
# This means that these are the project roots
# that are shared by all libraries in this repo.
PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
# This relative path is for include files between libraries.
# If an absolut path is used, this path will not be portable.
PROJECT_RELATIVE_ROOT := $(dir $(lastword $(MAKEFILE_LIST)))
# This evaluates to the path of the current working directory.
# i.e. The specific library under consideration.
LIBRARY_ROOT = $(PWD)

STANDARD_LIBRARY_PATH := $(PROJECT_ROOT)/dafny-dependencies/StandardLibrary
CODEGEN_CLI_ROOT := $(PROJECT_ROOT)/../codegen/smithy-dafny-codegen-cli
GRADLEW := $(PROJECT_ROOT)/../codegen/gradlew

########################## Dafny targets

# TODO: This target will not work for projects that use `replaceable` 
#       module syntax with multiple language targets.
# It will fail with error:
# Error: modules 'A' and 'B' both have CompileName 'same.extern.name'
# We need to come up with some way to verify files per-language.
# Rewrite this as part of Java implementation of LanguageSpecificLogic TestModel.

# Verify the entire project
verify:Z3_PROCESSES=$(shell echo $$(( $(CORES) >= 3 ? 2 : 1 )))
verify:DAFNY_PROCESSES=$(shell echo $$(( ($(CORES) - 1 ) / ($(CORES) >= 3 ? 2 : 1))))
verify:
	find . -name '*.dfy' | xargs -n 1 -P $(DAFNY_PROCESSES) -I % dafny \
		-vcsCores:$(Z3_PROCESSES) \
		-compile:0 \
		-definiteAssignment:3 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:300 \
		-trace \
		%

format:
	dafny format \
		--function-syntax 3 \
		--quantifier-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

format-check:
	dafny format \
		--check \
		--function-syntax 3 \
		--quantifier-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count 10000000 \
		TestResults/*.csv

# Dafny helper targets

# Transpile the entire project's impl
# For each index file listed in the project Makefile's PROJECT_INDEX variable,
#   append a `-library:TestModels/$(PROJECT_INDEX) to the transpiliation target
_transpile_implementation_all: TRANSPILE_DEPENDENCIES=$(patsubst %, -library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX))
_transpile_implementation_all: transpile_implementation

# The `$(OUT)` and $(TARGET) variables are problematic.
# Idealy they are different for every target call.
# However the way make evaluates variables
# having a target specific variable is hard.
# This all comes up because a project
# will need to also transpile its dependencies.
# This is worked around for now,
# by the fact that the `TARGET`
# for all these transpile calls will be the same.
# For `OUT` this is solved by makeing the paths realative.
# So that the runtime is express once
# and can be the same for all such runtimes.
# Since such targets are all shared,
# this is tractable.

# If the project under transpilation uses `replaceable` modules,
#   it MUST define a SRC_INDEX variable per language.
# SRC_INDEX points to the folder containing the `Index.dfy` file for a particular language
#   that `include`s all of that language's `replaces` modules.
# This variable's value might look like (ex.) `src/replaces/net` or `src/replaces/java`.
# If this variable is not provided, assume the project does not have `replaceable` modules,
#   and look for `Index.dfy` in the `src/` directory.
transpile_implementation: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
# `find` looks for `Index.dfy` files in either V1 or V2-styled project directories (single vs. multiple model files).
transpile_implementation:
	find ./dafny/**/$(SRC_INDEX_TRANSPILE)/ ./$(SRC_INDEX_TRANSPILE)/ -name 'Index.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
        -stdin \
        -noVerify \
        -vcsCores:$(CORES) \
        -compileTarget:$(TARGET) \
        -spillTargetCode:3 \
        -compile:0 \
        -optimizeErasableDatatypeWrapper:0 \
        -compileSuffix:1 \
        -quantifierSyntax:3 \
        -unicodeChar:0 \
        -functionSyntax:3 \
        -useRuntimeLib \
        -out $(OUT) \
        -library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
        $(TRANSPILE_DEPENDENCIES)

# If the project under transpilation uses `replaceable` modules,
#   it MUST define a SRC_INDEX variable per language.
# The purpose and usage of this is described in the `transpile_implementation` comments.
_transpile_test_all: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
# If the project under transpilation uses `replaceable` modules in its tests
#   it MUST define a TEST_INDEX variable per language.
# TEST_INDEX points to the folder containing all test files for a particular language.
# These files should use Dafny `include`s to include the generic test files as well.
# This variable's value might look like (ex.) `test/replaces/net` or `test/replaces/java`.
# If this variable is not provided, assume the project does not have `replaceable` modules,
#   and look for test files in the `test/` directory.
_transpile_test_all: TEST_INDEX_TRANSPILE=$(if $(TEST_INDEX),$(TEST_INDEX),test)
# If the Makefile defines DIR_STRUCTURE_V2 (i.e. multiple models/subprojects/services in project), then:
#   For each of this project's services defined in PROJECT_SERVICES:
#     append `-library:/path/to/Index.dfy` to the transpile target
# Else: (i.e. single model/service in project), then:
#   append `-library:/path/to/Index.dfy` to the transpile target
_transpile_test_all: TRANSPILE_DEPENDENCIES=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, -library:dafny/%/$(SRC_INDEX_TRANSPILE)/Index.dfy, $(PROJECT_SERVICES)), -library:$(SRC_INDEX_TRANSPILE)/Index.dfy)
# Transpile the entire project's tests
_transpile_test_all: transpile_test

# `find` looks for tests in either V1 or V2-styled project directories (single vs. multiple model files).
transpile_test:
	find ./dafny/**/$(TEST_INDEX_TRANSPILE) ./$(TEST_INDEX_TRANSPILE) -name "*.dfy" -name '*.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		-stdin \
		-noVerify \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:1 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		-library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
		$(TRANSPILE_DEPENDENCIES) \

transpile_dependencies:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) transpile_implementation_$(LANG)
	@$(foreach dependency, \
		$(PROJECT_DEPENDENCIES), \
		$(MAKE) -C $(PROJECT_ROOT)/$(dependency) transpile_implementation_$(LANG); \
	)

########################## Code-Gen targets

# The OUTPUT variables are created this way
# so that it is possible to run _parts_ of polymorph.
# Otherwise it is difficult to run/test only a Dafny change.
# Since they are defined per target
# a single target can decide what parts it wants to build.

# Pass in CODEGEN_CLI_ROOT in command line, e.g.
#   make polymorph_code_gen CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli
# StandardLibrary is filtered out from dependent-model patsubst list;
#   Its model is contained in $(LIBRARY_ROOT)/model, not $(LIBRARY_ROOT)/../StandardLibrary/Model.
_polymorph:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	$(DAFNY_VERSION_OPTION) \
	--library-root $(LIBRARY_ROOT) \
	--patch-files-dir $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/codegen-patches/$(SERVICE),$(LIBRARY_ROOT)/codegen-patches) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(OUTPUT_DAFNY) \
	$(OUTPUT_DOTNET) \
	$(OUTPUT_JAVA) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS)";

_polymorph_wrapped:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	$(DAFNY_VERSION_OPTION) \
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(OUTPUT_DAFNY_WRAPPED) \
	$(OUTPUT_DOTNET_WRAPPED) \
	$(OUTPUT_JAVA_WRAPPED) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(OUTPUT_LOCAL_SERVICE) \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS)";

_polymorph_dependencies:
	@$(foreach dependency, \
		$(PROJECT_DEPENDENCIES), \
		$(MAKE) -C $(PROJECT_ROOT)/$(dependency) polymorph_$(POLYMORPH_LANGUAGE_TARGET); \
	)

# Generates all target runtime code for all namespaces in this project.
.PHONY: polymorph_code_gen
polymorph_code_gen:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_code_gen ; \
	done

_polymorph_code_gen: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_code_gen: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_code_gen: _polymorph
_polymorph_code_gen: OUTPUT_DAFNY_WRAPPED=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET_WRAPPED=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped)
_polymorph_code_gen: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_code_gen: _polymorph_wrapped
_polymorph_code_gen: POLYMORPH_LANGUAGE_TARGET=code_gen
_polymorph_code_gen: _polymorph_dependencies

# Generates dafny code for all namespaces in this project
.PHONY: polymorph_dafny
polymorph_dafny:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) polymorph_dafny
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny ; \
	done

_polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
_polymorph_dafny: _polymorph_dependencies
_polymorph_dafny: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_dafny: _polymorph
_polymorph_dafny: OUTPUT_DAFNY_WRAPPED=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
    --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_dafny: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_dafny: _polymorph_wrapped

# Generates dotnet code for all namespaces in this project
.PHONY: polymorph_net
polymorph_net:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_net ; \
	done

_polymorph_net: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_net: _polymorph
_polymorph_net: OUTPUT_DOTNET_WRAPPED=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped)
_polymorph_net: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_net: _polymorph_wrapped
_polymorph_net: POLYMORPH_LANGUAGE_TARGET=net
_polymorph_net: _polymorph_dependencies

# Generates java code for all namespaces in this project
.PHONY: polymorph_java
polymorph_java:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_java ; \
	done

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph
_polymorph_java: OUTPUT_JAVA_WRAPPED=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_java: _polymorph_wrapped
_polymorph_java: POLYMORPH_LANGUAGE_TARGET=java
_polymorph_java: _polymorph_dependencies

# Dependency for formatting generating Java code
setup_prettier:
	npm i --no-save prettier prettier-plugin-java

########################## .NET targets

transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_implementation_net: _transpile_implementation_all

transpile_test_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_test_net: TEST_INDEX=$(NET_TEST_INDEX)
transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: _transpile_test_all

transpile_dependencies_net: LANG=net
transpile_dependencies_net: transpile_dependencies

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_brew:
	DYLD_LIBRARY_PATH="$(brew --prefix)/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/

########################## Java targets

build_java: transpile_java mvn_local_deploy_dependencies
	gradle -p runtimes/java build

transpile_java: | transpile_implementation_java transpile_test_java transpile_dependencies_java

transpile_implementation_java: TARGET=java
transpile_implementation_java: OUT=runtimes/java/ImplementationFromDafny
transpile_implementation_java: _transpile_implementation_all _mv_implementation_java

transpile_test_java: TARGET=java
transpile_test_java: OUT=runtimes/java/TestsFromDafny
transpile_test_java: _transpile_test_all _mv_test_java

# Currently Dafny compiles to Java by changing the directory name.
# Java puts things under a `java` directory.
# To avoid `java/implementation-java` the code is generated and then moved.
_mv_implementation_java:
	rm -rf runtimes/java/src/main/dafny-generated
	mv runtimes/java/ImplementationFromDafny-java runtimes/java/src/main/dafny-generated
_mv_test_java:
	rm -rf runtimes/java/src/test/dafny-generated
	mkdir -p runtimes/java/src/test
	mv runtimes/java/TestsFromDafny-java runtimes/java/src/test/dafny-generated

transpile_dependencies_java: LANG=java
transpile_dependencies_java: transpile_dependencies

mvn_local_deploy_dependencies:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) mvn_local_deploy
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% mvn_local_deploy;, $(LIBRARIES))

# The Java MUST all exist already through the transpile step.
mvn_local_deploy:
	gradle -p runtimes/java publishToMavenLocal

test_java:
	gradle -p runtimes/java runTests

_clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj

clean: _clean
