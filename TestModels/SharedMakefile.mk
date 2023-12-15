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

# Later versions of Dafny no longer default to adding "_Compile"
# to the names of modules when translating.
# Our target language code still assumes it does,
# so IF the /compileSuffix option is available in our verion of Dafny
# we need to provide it.
COMPILE_SUFFIX_OPTION_CHECK_EXIT_CODE := $(shell dafny /help | grep -q /compileSuffix; echo $$?)
ifeq ($(COMPILE_SUFFIX_OPTION_CHECK_EXIT_CODE), 0)
	COMPILE_SUFFIX_OPTION := -compileSuffix:1
else
	COMPILE_SUFFIX_OPTION :=
endif

STANDARD_LIBRARY_PATH := $(PROJECT_ROOT)/dafny-dependencies/StandardLibrary
CODEGEN_CLI_ROOT := $(PROJECT_ROOT)/../codegen/smithy-dafny-codegen-cli
GRADLEW := $(PROJECT_ROOT)/../codegen/gradlew

########################## Dafny targets

# TODO: This target does not work for projects using replaceable module syntax.
# It will fail with error
# Error: modules 'A' and 'B' both have CompileName 'same.extern.name'
# Fix this as part of https://sim.amazon.com/issues/CrypTool-5259
verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:300 \
		-trace \
		`find . -name '*.dfy'`

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
transpile_implementation:
	dafny \
        -vcsCores:$(CORES) \
        -compileTarget:$(TARGET) \
        -spillTargetCode:3 \
        -compile:0 \
        -optimizeErasableDatatypeWrapper:0 \
        $(COMPILE_SUFFIX_OPTION) \
        -quantifierSyntax:3 \
        -unicodeChar:0 \
        -functionSyntax:3 \
        -useRuntimeLib \
        -out $(OUT) \
        src/Index.dfy \
        -library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
        $(patsubst %, -library:$(PROJECT_ROOT)/%/src/Index.dfy, $(LIBRARIES))

# transpile_implementation_v2 SHOULD be based on `dafny translate` to use `outer-module`.
# This requires some Smithy-Dafny Dotnet codegen changes to drop the `_Compile` suffix from generated .NET code,
#   which requires that we identify how to decide when to include the `_Compile` suffix.
# One option is to generate `_Compile` for older Dafny versions,
#   and peg some Dafny version as the version that requires Smithy-Dafny to use `outer-module`.
# For now, leave as `dafny`, and comment out the corresponding `dafny translate` command.
transpile_implementation_v2: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src/Index.dfy)
transpile_implementation_v2:
	dafny \
        -vcsCores:$(CORES) \
        -compileTarget:$(TARGET) \
        -spillTargetCode:3 \
        -compile:0 \
        -optimizeErasableDatatypeWrapper:0 \
        $(COMPILE_SUFFIX_OPTION) \
        -quantifierSyntax:3 \
        -unicodeChar:0 \
        -functionSyntax:3 \
        -useRuntimeLib \
        -out $(OUT) \
        $(SRC_INDEX_TRANSPILE) \
        -library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
        $(patsubst %, -library:$(PROJECT_ROOT)/%/src/Index.dfy, $(LIBRARIES))

# transpile_implementation_v2 will have the following changes from transpile_implementation:
# - No option to append a `_Compile` suffix to module names without :extern.
#   This option is legacy, and is not exposed to `dafny translate`.
#   This flag will never be appended to code generated using this target.
#   When migrating a project to build using transpile_implementation_v2,
#     the developer must replace manually-written references to `_Compile`.
# - Makefiles may optionally supply a string pointing to the Index of generated code.
#   If the project under generation uses the V2 extern system (`replaceable` modules),
#     the project MUST supply a variable here pointing to an Index file that
#     `replaces` any `replaceable` modules with extern names that are idiomatic
#     to the language under generation.
#
# 	dafny translate \
# 	    $(TARGET) \
#         $(SRC_INDEX_TRANSPILE) \
#         --cores:$(CORES) \
#         --optimize-erasable-datatype-wrapper:false \
#         --quantifier-syntax:3 \
#         --unicode-char:false \
#         --function-syntax:3 \
#         --output:$(OUT) \
#         --library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
#         $(patsubst %, --library:$(PROJECT_ROOT)/%/$(SRC_INDEX_TRANSPILE), $(LIBRARIES))

transpile_test:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		$(COMPILE_SUFFIX_OPTION) \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

# transpile_test_v2 will have the following changes from transpile_test:
# - No option to append a `_Compile` suffix to module names without :extern.
#   This option is legacy, and is not exposed to `dafny translate`.
#   This flag will never be appended to code generated using this target.
#   When migrating a project to build using transpile_implementation_v2,
#     the developer must replace manually-written references to `_Compile`.
# - Makefiles may optionally supply a string pointing to the Index of generated code,
#     and the Index of test code.
#   If the project under generation uses the V2 extern system (`replaceable` modules),
#     the project MUST supply variables here pointing to Index files that
#     `replace` any `replaceable` modules with extern names that are idiomatic
#     to the language under generation.
# This is a PLACEHOLDER command. This is intended to be based on `dafny translate`
#   to allow use of `outer-module`.
# However, `dafny translate` lacks a `runAllTests` option.
# GHI: https://github.com/dafny-lang/dafny/issues/4888
transpile_test_v2: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src/Index.dfy)
transpile_test_v2: TEST_INDEX_TRANSPILE=$(if $(TEST_INDEX),$(TEST_INDEX),`find ./test -name '*.dfy'`)
transpile_test_v2:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		$(COMPILE_SUFFIX_OPTION) \
		-quantifierSyntax:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		$(TEST_INDEX_TRANSPILE) \
		-library:$(SRC_INDEX_TRANSPILE)

transpile_dependencies:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) transpile_implementation_$(LANG)
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_implementation_$(LANG);, $(LIBRARIES))

# We need this target to signal to some dependencies
# That they should transpile v2-compatible code
transpile_dependencies_v2:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) transpile_implementation_v2_$(LANG)
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_implementation_v2_$(LANG);, $(LIBRARIES))

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
	$(OUTPUT_DAFNY) \
	$(OUTPUT_DOTNET) \
	$(OUTPUT_JAVA) \
	--model $(LIBRARY_ROOT)/Model \
	--dependent-model $(PROJECT_ROOT)/dafny-dependencies/Model \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $(LIBRARIES)) \
	--namespace $(NAMESPACE) \
	$(AWS_SDK_CMD)";

_polymorph_wrapped:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	$(DAFNY_VERSION_OPTION) \
	$(OUTPUT_DAFNY_WRAPPED) \
	$(OUTPUT_DOTNET_WRAPPED) \
	$(OUTPUT_JAVA_WRAPPED) \
	--model $(LIBRARY_ROOT)/Model \
	--dependent-model $(PROJECT_ROOT)/dafny-dependencies/Model \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $(LIBRARIES)) \
	--namespace $(NAMESPACE) \
	$(OUTPUT_LOCAL_SERVICE) \
	$(AWS_SDK_CMD)";

_polymorph_dependencies:
	@$(foreach dependency, \
 			   $(DEPENDENT-MODELS), \
 			   cd $(PROJECT_ROOT)/$(dependency); \
 			   $(MAKE) -C $(PROJECT_ROOT)/$(dependency) polymorph_$(POLYMORPH_LANGUAGE_TARGET); \
	   )

# `polymorph_code_gen` is the generate-for-multiple-languages target
polymorph_code_gen: OUTPUT_DAFNY=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
polymorph_code_gen: OUTPUT_DOTNET=--output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/
polymorph_code_gen: _polymorph
# Generate wrapped code for all languages that support wrapped services
polymorph_code_gen: OUTPUT_DAFNY_WRAPPED=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
polymorph_code_gen: OUTPUT_DOTNET_WRAPPED=--output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped
polymorph_code_gen: OUTPUT_LOCAL_SERVICE=--local-service-test
polymorph_code_gen: _polymorph_wrapped
polymorph_code_gen: POLYMORPH_LANGUAGE_TARGET=code_gen
polymorph_code_gen: _polymorph_dependencies

polymorph_dafny: OUTPUT_DAFNY=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
polymorph_dafny: _polymorph
polymorph_dafny: OUTPUT_DAFNY_WRAPPED=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
polymorph_dafny: OUTPUT_LOCAL_SERVICE=--local-service-test
polymorph_dafny: _polymorph_wrapped
polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
polymorph_dafny: _polymorph_dependencies

polymorph_net: OUTPUT_DOTNET=--output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/
polymorph_net: _polymorph
polymorph_net: OUTPUT_DOTNET_WRAPPED=--output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped
polymorph_net: OUTPUT_LOCAL_SERVICE=--local-service-test
polymorph_net: _polymorph_wrapped
polymorph_net: POLYMORPH_LANGUAGE_TARGET=net
polymorph_net: _polymorph_dependencies

polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
polymorph_java: _polymorph
polymorph_java: OUTPUT_JAVA_WRAPPED=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
polymorph_java: OUTPUT_LOCAL_SERVICE=--local-service-test
polymorph_java: _polymorph_wrapped
polymorph_java: POLYMORPH_LANGUAGE_TARGET=java
polymorph_java: _polymorph_dependencies

########################## .NET targets

transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net
transpile_net_v2: | transpile_implementation_v2_net transpile_test_v2_net transpile_dependencies_v2_net

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: transpile_implementation

transpile_implementation_v2_net: TARGET=cs
transpile_implementation_v2_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_v2_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_implementation_v2_net: transpile_implementation_v2

transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: transpile_test

transpile_test_v2_net: TARGET=cs
transpile_test_v2_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_v2_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_test_v2_net: TEST_INDEX=$(NET_TEST_INDEX)
transpile_test_v2_net: transpile_test

transpile_dependencies_net: LANG=net
transpile_dependencies_net: transpile_dependencies

transpile_dependencies_v2_net: LANG=net
transpile_dependencies_v2_net: transpile_dependencies_v2

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
transpile_implementation_java: transpile_implementation _mv_implementation_java

transpile_test_java: TARGET=java
transpile_test_java: OUT=runtimes/java/TestsFromDafny
transpile_test_java: transpile_test _mv_test_java

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
