# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These are make targets that can be shared between all projects
# that use a common layout.
# They will only function if executed inside a project directory.
# See https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/TestModels
# for examples.

# There are several variables that are used here.
# The expectation is to define these variables
# inside each project.

# Variables:
# MAX_RESOURCE_COUNT -- The Dafny verification max resource count.
# 	This is is per project because the verification variability can differ.
#   Individual functions/methods/lemmas can override this limit using `{:rlimit N}`,
#   but be aware that the attribute multiplies N by 1000!
# VERIFY_TIMEOUT -- The Dafny verification timeout in seconds.
# 	This is only a guard against builds taking way too long to fail.
#   The resource count limit above is much more important for fighting brittle verification.
# PROJECT_DEPENDENCIES -- List of dependencies for the project.
# 	It should be the list of top level directory names
# PROJECT_SERVICES -- List of names of each local service in the project
# SERVICE_NAMESPACE_<service> -- for each service in PROJECT_SERVICES,
#   the list of dependencies for that smithy namespace. It should be a list
#   of Model directories
# SERVICE_DEPS_<service> -- for each service in PROJECT_SERVICES,
#   the list of dependencies for that smithy namespace. It should be a list
#   of Model directories
# AWS_SDK_CMD -- the `--aws-sdk` command to generate AWS SDK style interfaces.
# STD_LIBRARY -- path from this file to the StandardLibrary Dafny project.
# SMITHY_DEPS -- path from this file to smithy dependencies, such as custom traits.
# GRADLEW -- the gradlew to use when building Java runtimes.
#   defaults to $(SMITHY_DAFNY_ROOT)/codegen/gradlew

MAX_RESOURCE_COUNT := 10000000
VERIFY_TIMEOUT := 100

# This evaluates to the path of the current working directory.
# i.e. The specific library under consideration.
LIBRARY_ROOT := $(shell pwd)
# Smithy Dafny code gen needs to know
# where the smithy model is.
# This is generally in the same directory as the library.
# However in the case of a wrapped library,
# such as the test vectors
# the implementation MAY be in a different library
# than the model.
# By having two related variables
# test vector projects can point to
# the specific model they need
# but still build everything in their local library directory.
SMITHY_MODEL_ROOT := $(LIBRARY_ROOT)/Model

CODEGEN_CLI_ROOT := $(SMITHY_DAFNY_ROOT)/codegen/smithy-dafny-codegen-cli
GRADLEW := $(SMITHY_DAFNY_ROOT)/codegen/gradlew

DAFNY_VERSION := $(shell $(SMITHY_DAFNY_ROOT)/scripts/check_dafny_version.sh)

include $(SMITHY_DAFNY_ROOT)/SmithyDafnySedMakefile.mk

# This flag enables pre-processing on extern module names.
# This pre-processing is required to compile to Python and Go.
# This is disabled by default.
# This should be enabled in each individual project's Makefile if that project compiles to Python or Go.
# This can be enabled by setting this variable to any nonempty value (ex. true, 1)
ENABLE_EXTERN_PROCESSING?=

########################## Dafny targets

# Proof of correctness for the math below
#  function Z3_PROCESSES(cpus:nat): nat
#  { if cpus >= 3 then 2 else 1 }

#  function DAFNY_PROCESSES(cpus: nat): nat
#   requires 0 < cpus // 0 cpus would do no work!
#  { (cpus - 1 )/Z3_PROCESSES(cpus) }

#  lemma Correct(cpus:nat)
#    ensures DAFNY_PROCESSES(cpus) * Z3_PROCESSES(cpus) <= cpus
#  {}

# Verify the entire project
verify:Z3_PROCESSES=$(shell echo $$(( $(CORES) >= 3 ? 2 : 1 )))
verify:DAFNY_PROCESSES=$(shell echo $$(( ($(CORES) - 1 ) / ($(CORES) >= 3 ? 2 : 1))))
# TODO: remove dafny_options from all targets in the future
# and leave it up to the UX to decide which options they want to add
verify:DAFNY_OPTIONS=--allow-warnings
verify:
	find . -name '*.dfy' | xargs -n 1 -P $(DAFNY_PROCESSES) -I % dafny verify \
		--cores $(Z3_PROCESSES) \
		--unicode-char false \
		--function-syntax 3 \
		--log-format csv \
		--verification-time-limit $(VERIFY_TIMEOUT) \
		--resource-limit $(MAX_RESOURCE_COUNT) \
		$(DAFNY_OPTIONS) \
		%

# Verify single file FILE with text logger.
# This is useful for debugging resource count usage within a file.
# Use PROC to further scope the verification
verify_single:DAFNY_OPTIONS=--allow-warnings
verify_single:
	dafny verify \
		--cores $(CORES) \
		--unicode-char false \
		--function-syntax 3 \
		--log-format text \
		--verification-time-limit $(VERIFY_TIMEOUT) \
		--resource-limit $(MAX_RESOURCE_COUNT) \
		$(DAFNY_OPTIONS) \
		$(if ${PROC},-proc:*$(PROC)*,) \
		$(FILE)

#Verify only a specific namespace at env var $(SERVICE)
verify_service:DAFNY_OPTIONS=--allow-warnings
verify_service:
	@: $(if ${SERVICE},,$(error You must pass the SERVICE to generate for));
	dafny verify \
		--cores $(CORES) \
		--unicode-char false \
		--function-syntax 3 \
		--log-format text \
		--verification-time-limit $(VERIFY_TIMEOUT) \
		--resource-limit $(MAX_RESOURCE_COUNT) \
		$(DAFNY_OPTIONS) \
		`find ./dafny/$(SERVICE) -name '*.dfy'` \

format_dafny:
	dafny format \
		--function-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

format_dafny-check:
	dafny format \
		--check \
		--function-syntax 3 \
		--unicode-char false \
		`find . -name '*.dfy'`

# This no longer enforces the maximum resource count,
# as we're passing /rlimit to dafny directly now.
# But it's still useful information to see what assertion batches
# are close to the limit.
dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		TestResults/*.csv

clean-dafny-report:
	rm TestResults/*.csv

# Dafny helper targets

# Transpile the entire project's impl
# For each index file listed in the project Makefile's PROJECT_INDEX variable,
#   append a `-library:TestModels/$(PROJECT_INDEX) to the transpiliation target
_transpile_implementation_all: TRANSPILE_DEPENDENCIES=$(patsubst %, --library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX))
_transpile_implementation_all: transpile_implementation 


# The `$(OUT)` and $(TARGET) variables are problematic.
# Ideally they are different for every target call.
# However the way make evaluates variables
# having a target specific variable is hard.
# This all comes up because a project
# will need to also transpile its dependencies.
# This is worked around for now,
# by the fact that the `TARGET`
# for all these transpile calls will be the same.
# For `OUT` this is solved by making the paths relative.
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
# At this time it is *significatly* faster
# to give Dafny a single file
# that includes everything
# than it is to pass each file to the CLI.
# ~2m vs ~10s for our large projects.
# Also the expectation is that verification happens in the `verify` target
# `find` looks for `Index.dfy` files in either V1 or V2-styled project directories (single vs. multiple model files).
transpile_implementation:
	find ./dafny/**/$(SRC_INDEX_TRANSPILE)/ ./$(SRC_INDEX_TRANSPILE)/ -name 'Index.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
	translate $(TARGET) \
		--stdin \
		--no-verify \
		--cores:$(CORES) \
		--optimize-erasable-datatype-wrapper:false \
		--unicode-char:false \
		--function-syntax:3 \
		--output $(OUT) \
		$(DAFNY_OPTIONS) \
		$(DAFNY_OTHER_FILES) \
		$(TRANSPILE_MODULE_NAME) \
		$(if $(strip $(STD_LIBRARY)) , --library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSLATION_RECORD) \
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
_transpile_test_all: TRANSPILE_DEPENDENCIES=$(if ${DIR_STRUCTURE_V2}, $(patsubst %, --library:dafny/%/$(SRC_INDEX_TRANSPILE)/Index.dfy, $(PROJECT_SERVICES)), --library:$(SRC_INDEX_TRANSPILE)/Index.dfy)
# Transpile the entire project's tests
_transpile_test_all: transpile_test

transpile_test:
	find ./dafny/**/$(TEST_INDEX_TRANSPILE) ./$(TEST_INDEX_TRANSPILE) -name "*.dfy" -name '*.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		translate $(TARGET) \
		--stdin \
		--no-verify \
		--cores:$(CORES) \
		--optimize-erasable-datatype-wrapper:false \
		--unicode-char:false \
		--function-syntax:3 \
		--output $(OUT) \
		$(DAFNY_OPTIONS) \
		$(DAFNY_OTHER_FILES) \
		$(if $(strip $(STD_LIBRARY)) , --library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy, ) \
		$(TRANSLATION_RECORD) \
		$(SOURCE_TRANSLATION_RECORD) \
		$(TRANSPILE_MODULE_NAME) \
		$(TRANSPILE_DEPENDENCIES) \

# If we are not the StandardLibrary, transpile the StandardLibrary.
# Transpile all other dependencies
transpile_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) transpile_implementation_$(LANG), )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_implementation_$(LANG);, $(PROJECT_DEPENDENCIES))

transpile_dependencies_test:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) transpile_test_$(LANG), )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% transpile_test_$(LANG);, $(PROJECT_DEPENDENCIES))

########################## Code-Gen targets

mvn_local_deploy_polymorph_dependencies:
	$(MAKE) -C $(SMITHY_DAFNY_ROOT) mvn_local_deploy_polymorph_dependencies

# The OUTPUT variables are created this way
# so that it is possible to run _parts_ of polymorph.
# Otherwise it is difficult to run/test only a Dafny change.
# Since they are defined per target
# a single target can decide what parts it wants to build.

# Pass in CODEGEN_CLI_ROOT in command line, e.g.
#   make polymorph_code_gen CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli
# StandardLibrary is filtered out from dependent-model patsubst list;
#   Its model is contained in $(LIBRARY_ROOT)/model, not $(LIBRARY_ROOT)/../StandardLibrary/Model.
_polymorph: mvn_local_deploy_polymorph_dependencies
_polymorph:
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	--patch-files-dir $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/codegen-patches/$(SERVICE),$(LIBRARY_ROOT)/codegen-patches) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(INPUT_DAFNY) \
	$(OUTPUT_DAFNY) \
	$(OUTPUT_JAVA) \
	$(OUTPUT_JAVA_TEST) \
	$(OUTPUT_DOTNET) \
	$(OUTPUT_GO) \
	$(OUTPUT_PYTHON) \
	$(MODULE_NAME) \
	$(OUTPUT_RUST) \
	--model $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(SMITHY_MODEL_ROOT)) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	$(DEPENDENCY_MODULE_NAMES) \
	$(patsubst %, --namespace %, $($(namespace_var))) \
	$(OUTPUT_LOCAL_SERVICE_$(SERVICE)) \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS) \
    ";

_polymorph_wrapped: mvn_local_deploy_polymorph_dependencies
_polymorph_wrapped:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	$(INPUT_DAFNY) \
	$(OUTPUT_DAFNY_WRAPPED) \
	$(OUTPUT_DOTNET_WRAPPED) \
	$(OUTPUT_JAVA_WRAPPED) \
	$(OUTPUT_GO_WRAPPED) \
	$(OUTPUT_PYTHON_WRAPPED) \
	$(MODULE_NAME) \
	$(OUTPUT_RUST_WRAPPED) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	$(DEPENDENCY_MODULE_NAMES) \
	--namespace $($(namespace_var)) \
	--local-service-test \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS)";

_polymorph_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) polymorph_$(POLYMORPH_LANGUAGE_TARGET) LIBRARY_ROOT=$(PROJECT_ROOT)/$(STD_LIBRARY), )
	@$(foreach dependency, \
		$(PROJECT_DEPENDENCIES), \
		$(MAKE) -C $(PROJECT_ROOT)/$(dependency) polymorph_$(POLYMORPH_LANGUAGE_TARGET); \
	)

# Generates all target runtime code for all namespaces in this project.
# Not including Rust until is it more fully implemented.
.PHONY: polymorph_code_gen
polymorph_code_gen: POLYMORPH_LANGUAGE_TARGET=code_gen
polymorph_code_gen: _polymorph_dependencies
polymorph_code_gen:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_code_gen ; \
	done

_polymorph_code_gen: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_code_gen: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_code_gen: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_code_gen: OUTPUT_GO=--output-go $(LIBRARY_ROOT)/runtimes/go/
_polymorph_code_gen: OUTPUT_JAVA_TEST=--output-java-test $(LIBRARY_ROOT)/runtimes/java/src/test/smithy-generated
_polymorph_code_gen: _polymorph

check_polymorph_diff:
	git diff --exit-code $(LIBRARY_ROOT) || (echo "ERROR: polymorph-generated code does not match the committed code - see above for diff. Either commit the changes or regenerate with 'POLYMORPH_OPTIONS=--update-patch-files'." && exit 1)

# Generates dafny code for all namespaces in this project
.PHONY: polymorph_dafny
polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
polymorph_dafny: _polymorph_dependencies
polymorph_dafny:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny ; \
	done

_polymorph_dafny: OUTPUT_DAFNY=\
		--output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_dafny: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dafny: _polymorph

# Generates dotnet code for all namespaces in this project
.PHONY: polymorph_dotnet
polymorph_dotnet: POLYMORPH_LANGUAGE_TARGET=dotnet
polymorph_dotnet: _polymorph_dependencies
polymorph_dotnet:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dotnet ; \
	done

_polymorph_dotnet: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_dotnet: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dotnet: _polymorph

# Generates java code for all namespaces in this project
.PHONY: polymorph_java
polymorph_java: POLYMORPH_LANGUAGE_TARGET=java
polymorph_java: _polymorph_dependencies
polymorph_java:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_java ; \
	done

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: OUTPUT_JAVA_TEST=--output-java-test $(LIBRARY_ROOT)/runtimes/java/src/test/smithy-generated
_polymorph_java: INPUT_DAFNY=\
	--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_java: _polymorph

# Generates python code for all namespaces in this project
.PHONY: polymorph_python
polymorph_python: POLYMORPH_LANGUAGE_TARGET=python
polymorph_python: _polymorph_dependencies
polymorph_python:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_python ; \
	done

_polymorph_python: OUTPUT_PYTHON=--output-python $(LIBRARY_ROOT)/runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
# Defined per-Makefile
_polymorph_python: MODULE_NAME=--library-name $(PYTHON_MODULE_NAME)
# Defined per-Makefile
_polymorph_python: DEPENDENCY_MODULE_NAMES=$(PYTHON_DEPENDENCY_MODULE_NAMES)
_polymorph_python: _polymorph

# Dependency for formatting generating Java code
setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5

# Generates rust code for all namespaces in this project
.PHONY: polymorph_rust

polymorph_rust:
	$(MAKE) _polymorph_rust

_polymorph_rust: POLYMORPH_LANGUAGE_TARGET=rust
_polymorph_rust: service_deps_var=SERVICE_DEPS_$(MAIN_SERVICE_FOR_RUST)
_polymorph_rust: namespace_var=SERVICE_NAMESPACE_$(MAIN_SERVICE_FOR_RUST)
_polymorph_rust: SERVICE=$(MAIN_SERVICE_FOR_RUST)
_polymorph_rust: OUTPUT_RUST=--output-rust $(LIBRARY_ROOT)/runtimes/rust
# For several TestModels we've just manually written the code generation target,
# So we just want to ensure we can transpile and pass the tests in CI.
# For those, make polymorph_rust should just be a no-op.
_polymorph_rust: $(if $(RUST_BENERATED), , _polymorph)

###########################

.PHONY: polymorph_go
polymorph_go: POLYMORPH_LANGUAGE_TARGET=go
polymorph_go: _polymorph_dependencies
polymorph_go:
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_go ; \
	done

_polymorph_go: OUTPUT_GO=--output-go $(LIBRARY_ROOT)/runtimes/go/
_polymorph_go: MODULE_NAME=--library-name $(GO_MODULE_NAME)
_polymorph_go: DEPENDENCY_MODULE_NAMES = $(GO_DEPENDENCY_MODULE_NAMES)
# TODO: run_goimports should be an independent command. Right now it is required because of import issues in polymorph_go
_polymorph_go: _polymorph _mv_polymorph_go run_goimports

run_goimports:
	cd runtimes/go/ImplementationFromDafny-go && goimports -w .
	@if [ -d runtimes/go/TestsFromDafny-go ]; then \
		cd runtimes/go/TestsFromDafny-go && goimports -w . ; \
	fi

_gomod_init:
	#TODO: Think about handwritten go.mod
	@(cd $(LIBRARY_ROOT)/runtimes/go/TestsFromDafny-go && \
		if [ -f go.mod ]; then rm -f go.mod; fi && \
		go mod init $(GO_MODULE_NAME) && \
		echo "require github.com/dafny-lang/DafnyStandardLibGo v0.0.0" >> go.mod && \
		echo "require github.com/dafny-lang/DafnyRuntimeGo v0.0.0" >> go.mod && \
		if [ $$(basename $$(dirname $(LIBRARY_ROOT))) == "SimpleTypes" ]; then \
			echo "replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../../DafnyRuntimeGo/" >> go.mod; \
			echo "replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/" >> go.mod; \
		else \
			echo "replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/" >> go.mod; \
			echo "replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/" >> go.mod; \
		fi && \
		go mod tidy)

_mv_polymorph_go:
	@for dir in $(LIBRARY_ROOT)/runtimes/go/* ; do \
        if [ "$$(basename $$dir)" != "ImplementationFromDafny-go" ] && [ "$$(basename $$dir)" != "TestsFromDafny-go" ]; then \
			cp -Rf $$dir runtimes/go/ImplementationFromDafny-go/; \
			cp -Rf $$dir runtimes/go/TestsFromDafny-go/; \
			rm -r $$dir; \
		fi \
    done
########################## .NET targets

net: polymorph_dafny transpile_net polymorph_dotnet test_net

transpile_net: $(if $(ENABLE_EXTERN_PROCESSING), _with_extern_pre_transpile, )
transpile_net: | transpile_implementation_net transpile_test_net transpile_dependencies_net
transpile_net: $(if $(ENABLE_EXTERN_PROCESSING), _with_extern_post_transpile, )

transpile_implementation_net: TARGET=cs
transpile_implementation_net: OUT=runtimes/net/ImplementationFromDafny
transpile_implementation_net: DAFNY_OPTIONS=--allow-warnings --include-test-runner --compile-suffix
transpile_implementation_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_implementation_net: _transpile_implementation_all

transpile_test_net: SRC_INDEX=$(NET_SRC_INDEX)
transpile_test_net: TEST_INDEX=$(NET_TEST_INDEX)
transpile_test_net: DAFNY_OPTIONS=--allow-warnings --include-test-runner --compile-suffix
transpile_test_net: TARGET=cs
transpile_test_net: OUT=runtimes/net/tests/TestsFromDafny
transpile_test_net: _transpile_test_all

transpile_dependencies_net: LANG=net
transpile_dependencies_net: transpile_dependencies

test_net: FRAMEWORK=net6.0
test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

test_net_mac_intel: FRAMEWORK=net6.0
test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

test_net_mac_brew: FRAMEWORK=net6.0
test_net_mac_brew:
	DYLD_LIBRARY_PATH="$(shell brew --prefix)/opt/openssl@1.1/lib/" dotnet run \
		--project runtimes/net/tests/ \
		--framework $(FRAMEWORK)

setup_net:
	dotnet restore runtimes/net/

format_net:
	dotnet format runtimes/net/*.csproj

format_net-check:
	dotnet format runtimes/net/*.csproj --verify-no-changes

########################## Java targets

java: polymorph_dafny transpile_java polymorph_java build_java test_java

build_java: transpile_java mvn_local_deploy_dependencies
	$(GRADLEW) -p runtimes/java build

transpile_java: $(if $(ENABLE_EXTERN_PROCESSING), _with_extern_pre_transpile, )
transpile_java: | transpile_implementation_java transpile_test_java transpile_dependencies_java
transpile_java: $(if $(ENABLE_EXTERN_PROCESSING), _with_extern_post_transpile, )

transpile_implementation_java: TARGET=java
transpile_implementation_java: DAFNY_OPTIONS=--allow-warnings --include-test-runner --compile-suffix
transpile_implementation_java: OUT=runtimes/java/ImplementationFromDafny
transpile_implementation_java: _transpile_implementation_all _mv_implementation_java

transpile_test_java: TARGET=java
transpile_test_java: DAFNY_OPTIONS=--allow-warnings --include-test-runner --compile-suffix
transpile_test_java: OUT=runtimes/java/TestsFromDafny
transpile_test_java: _transpile_test_all _mv_test_java

# Currently Dafny compiles to Java by changing the directory name.
# Java puts things under a `java` directory.
# To avoid `java/implementation-java` the code is generated and then moved.
_mv_implementation_java:
	rm -rf runtimes/java/src/main/dafny-generated
	mkdir -p runtimes/java/src/main
	mv runtimes/java/ImplementationFromDafny-java runtimes/java/src/main/dafny-generated
_mv_test_java:
	rm -rf runtimes/java/src/test/dafny-generated
	mkdir -p runtimes/java/src/test
	mv runtimes/java/TestsFromDafny-java runtimes/java/src/test/dafny-generated

transpile_dependencies_java: LANG=java
transpile_dependencies_java: transpile_dependencies

# If we are not StandardLibrary, locally deploy the StandardLibrary.
# Locally deploy all other dependencies 
mvn_local_deploy_dependencies:
	$(if $(strip $(STD_LIBRARY)), $(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) mvn_local_deploy, )
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% mvn_local_deploy;, $(PROJECT_DEPENDENCIES))

# The Java MUST all exist already through the transpile step.
mvn_local_deploy:
	$(GRADLEW) -p runtimes/java publishMavenLocalPublicationToMavenLocal

# The Java MUST all exsist if we want to publish to CodeArtifact
mvn_ca_deploy:
	$(GRADLEW) -p runtimes/java publishMavenPublicationToPublishToCodeArtifactCIRepository

mvn_staging_deploy:
	$(GRADLEW) -p runtimes/java publishMavenPublicationToPublishToCodeArtifactStagingRepository

test_java:
	$(GRADLEW) -p runtimes/java runTests
	$(GRADLEW) -p runtimes/java test --info

########################## Rust targets

rust: polymorph_dafny transpile_rust polymorph_rust test_rust

# The Dafny Rust code generator only supports a single crate for everything,
# so (among other consequences) we compile src and test code together.
transpile_rust: | transpile_implementation_rust

transpile_implementation_rust: TARGET=rs
transpile_implementation_rust: OUT=implementation_from_dafny
transpile_implementation_rust: SRC_INDEX=$(RUST_SRC_INDEX)
transpile_implementation_rust: TEST_INDEX=$(RUST_TEST_INDEX)
# The Dafny Rust code generator is not complete yet,
# so we want to emit code even if there are unsupported features in the input.
transpile_implementation_rust: DAFNY_OPTIONS=--emit-uncompilable-code --allow-warnings --compile-suffix
# The Dafny Rust code generator only supports a single crate for everything,
# so we inline all dependencies by not passing `-library` to Dafny.
transpile_implementation_rust: TRANSPILE_DEPENDENCIES=
transpile_implementation_rust: STD_LIBRARY=
transpile_implementation_rust: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
transpile_implementation_rust: TEST_INDEX_TRANSPILE=$(if $(TEST_INDEX),$(TEST_INDEX),test)
transpile_implementation_rust: DAFNY_OTHER_FILES=$(RUST_OTHER_FILES)
transpile_implementation_rust: $(if $(TRANSPILE_TESTS_IN_RUST), transpile_test, transpile_implementation) _mv_implementation_rust patch_after_transpile_rust

transpile_dependencies_rust: LANG=rust
transpile_dependencies_rust: transpile_dependencies

_mv_implementation_rust:
	mkdir -p runtimes/rust/src
	mv implementation_from_dafny-rust/src/implementation_from_dafny.rs runtimes/rust/src/implementation_from_dafny.rs
# rustfmt has a recurring bug where it leaves behind trailing spaces and then complains about it.
# Pre-process the Dafny-generated Rust code to remove them.
	sed -i -e 's/[[:space:]]*$$//' runtimes/rust/src/implementation_from_dafny.rs 
	rm -f runtimes/rust/src/implementation_from_dafny.rs-e
	rustfmt --edition 2021 runtimes/rust/src/implementation_from_dafny.rs
	rm -rf implementation_from_dafny-rust

patch_after_transpile_rust:
	export service_deps_var=SERVICE_DEPS_$(MAIN_SERVICE_FOR_RUST) ; \
	export namespace_var=SERVICE_NAMESPACE_$(MAIN_SERVICE_FOR_RUST) ; \
	export SERVICE=$(MAIN_SERVICE_FOR_RUST) ; \
	$(MAKE) _patch_after_transpile_rust ; \

_patch_after_transpile_rust: OUTPUT_RUST=--output-rust $(LIBRARY_ROOT)/runtimes/rust
_patch_after_transpile_rust:
	cd $(CODEGEN_CLI_ROOT); \
	./../gradlew run --args="\
	patch-after-transpile \
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	$(OUTPUT_RUST) \
	--model $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(SMITHY_MODEL_ROOT)) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(AWS_SDK_CMD) \
	$(POLYMORPH_OPTIONS) \
	$(if $(TRANSPILE_TESTS_IN_RUST), --local-service-test, ) \
	";

build_rust:
	cd runtimes/rust; \
	cargo build

test_rust:
	cd runtimes/rust; \
	cargo test -- --nocapture

########################## Cleanup targets

_clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj

clean: _clean

########################## Go targets
transpile_go: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_pre_transpile, )
transpile_go: | transpile_dependencies_go transpile_implementation_go transpile_test_go
transpile_go: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_post_transpile, )

transpile_implementation_go: TARGET=go
transpile_implementation_go: OUT=runtimes/go/ImplementationFromDafny
transpile_implementation_go: DAFNY_OPTIONS=--allow-warnings
transpile_implementation_go: TRANSPILE_DEPENDENCIES=$(patsubst %, --library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX))
transpile_implementation_go: TRANSLATION_RECORD=$(patsubst %, --translation-record:$(PROJECT_ROOT)/%, $(TRANSLATION_RECORD_GO))
transpile_implementation_go: TRANSPILE_MODULE_NAME=--go-module-name $(GO_MODULE_NAME)
transpile_implementation_go: _transpile_implementation_all

transpile_test_go: TARGET=go
transpile_test_go: OUT=runtimes/go/TestsFromDafny
transpile_test_go: DAFNY_OPTIONS=--allow-warnings --include-test-runner
transpile_test_go: TRANSPILE_DEPENDENCIES=$(patsubst %, --library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX))
transpile_test_go: TRANSLATION_RECORD=$(patsubst %, --translation-record:$(PROJECT_ROOT)/%, $(TRANSLATION_RECORD_GO)) $(patsubst %, --translation-record:$(LIBRARY_ROOT)/%, runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr)
transpile_test_go: TRANSPILE_MODULE_NAME=--go-module-name $(GO_MODULE_NAME)/test
transpile_test_go: _transpile_test_all

transpile_dependencies_go: LANG=go
transpile_dependencies_go: transpile_dependencies

clean_go:
	rm -rf $(LIBRARY_ROOT)/runtimes/go/ImplementationFromDafny-go
	rm -rf $(LIBRARY_ROOT)/runtimes/go/TestsFromDafny-go

test_go:
	cd runtimes/go/TestsFromDafny-go && go mod tidy && go run TestsFromDafny.go

########################## Python targets

# Install packages via `python3 -m pip`,
# which is the syntax Smithy-Python and Smithy-Dafny Python use
# to invoke these packages.
# This helps ensure these packages are installed to the correct Python installation.
setup_smithy_dafny_python:
	python3 -m pip install docformatter black

setup_python: setup_smithy_dafny_python
setup_python:
	python3 -m pip install poetry

net: polymorph_dafny transpile_python polymorph_python test_python

# Python MUST transpile dependencies first to generate .dtr files
transpile_python: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_pre_transpile, )
transpile_python: | transpile_dependencies_python transpile_implementation_python transpile_test_python
transpile_python: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_post_transpile, )

# This target should ONLY be used if you KNOW .dtr files are present.
# This file will NOT transpile source code or source code dependencies,
# so it will not re-generaate .dtr files.
# The intended use case is to generate tests in release scripts without re-transpiling source code.
transpile_only_test_python: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_pre_transpile, )
transpile_only_test_python: transpile_test_python
transpile_only_test_python: $(if $(ENABLE_EXTERN_PROCESSING), _no_extern_post_transpile, )

transpile_implementation_python: DAFNY_OPTIONS=--allow-warnings --include-test-runner
transpile_implementation_python: TARGET=py
transpile_implementation_python: OUT=runtimes/python/dafny_src
transpile_implementation_python: SRC_INDEX=$(PYTHON_SRC_INDEX)
transpile_implementation_python: TRANSPILE_MODULE_NAME=--python-module-name=$(PYTHON_MODULE_NAME).internaldafny.generated
transpile_implementation_python: TRANSLATION_RECORD=$(TRANSLATION_RECORD_PYTHON)
transpile_implementation_python: _transpile_implementation_all _mv_implementation_python

transpile_test_python: TARGET=py
transpile_test_python: OUT=runtimes/python/dafny_test
transpile_test_python: DAFNY_OPTIONS=--allow-warnings --include-test-runner
transpile_test_python: SRC_INDEX=$(PYTHON_SRC_INDEX)
transpile_test_python: TEST_INDEX=$(PYTHON_TEST_INDEX)
transpile_test_python: TRANSLATION_RECORD=$(TRANSLATION_RECORD_PYTHON)
transpile_test_python: SOURCE_TRANSLATION_RECORD= --translation-record runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/dafny_src-py.dtr
transpile_test_python: _transpile_test_all _mv_test_python

# Move Dafny-generated code into its expected location in the Python module
_mv_implementation_python:
	# Remove any previously generated Dafny code in src/, then copy in newly-generated code
	rm -rf runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/
	mkdir -p runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/
	mv runtimes/python/dafny_src-py/* runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated
	rm -rf runtimes/python/dafny_src-py

_mv_test_python:
	# Remove any previously generated Dafny code in test/, then copy in newly-generated code
	rm -rf runtimes/python/test/internaldafny/generated
	mkdir -p runtimes/python/test/internaldafny/generated
	mv runtimes/python/dafny_test-py/* runtimes/python/test/internaldafny/generated
	rm -rf runtimes/python/dafny_test-py

transpile_dependencies_python: LANG=python
transpile_dependencies_python: transpile_dependencies

test_python:
	rm -rf runtimes/python/.tox
	python3 -m tox -c runtimes/python --verbose

########################## local testing targets

# These targets are added as a convenience for local development.
# If you experience weird behavior using these targets,
# fall back to the regular `build` or `test` targets.
# These targets MUST only be used for local testing,
# and MUST NOT be used in CI.

# Targets to transpile single local service for convenience.
# Specify the local service to build by passing a SERVICE env var.
# Note that this does not generate identical files as `transpile_implementation_java`

local_transpile_impl_java_single: TARGET=java
local_transpile_impl_java_single: OUT=runtimes/java/ImplementationFromDafny
local_transpile_impl_java_single: local_transpile_impl_single
	cp -R runtimes/java/ImplementationFromDafny-java/* runtimes/java/src/main/dafny-generated
	rm -rf runtimes/java/ImplementationFromDafny-java/

local_transpile_impl_net_single: TARGET=cs
local_transpile_impl_net_single: OUT=runtimes/net/ImplementationFromDafny
local_transpile_impl_net_single: local_transpile_impl_single

local_transpile_impl_rust_single: TARGET=rs
local_transpile_impl_rust_single: OUT=implementation_from_dafny
local_transpile_impl_rust_single: SRC_INDEX=$(RUST_SRC_INDEX)
local_transpile_impl_rust_single: TEST_INDEX=$(RUST_TEST_INDEX)
local_transpile_impl_rust_single: DAFNY_OPTIONS=--emit-uncompilable-code --allow-warnings --compile-suffix
local_transpile_impl_rust_single: TRANSPILE_DEPENDENCIES=
local_transpile_impl_rust_single: STD_LIBRARY=
local_transpile_impl_rust_single: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
local_transpile_impl_rust_single: TEST_INDEX_TRANSPILE=$(if $(TEST_INDEX),$(TEST_INDEX),test)
local_transpile_impl_rust_single: DAFNY_OTHER_FILES=$(RUST_OTHER_FILES)
local_transpile_impl_rust_single: deps_var=SERVICE_DEPS_$(SERVICE)
local_transpile_impl_rust_single: service_deps_var=SERVICE_DEPS_$(SERVICE)
local_transpile_impl_rust_single: namespace_var=SERVICE_NAMESPACE_$(SERVICE)
local_transpile_impl_rust_single: $(if $(TRANSPILE_TESTS_IN_RUST), transpile_test, transpile_implementation) _mv_implementation_rust _patch_after_transpile_rust


local_transpile_impl_single: deps_var=SERVICE_DEPS_$(SERVICE)
local_transpile_impl_single: TRANSPILE_TARGETS=./dafny/$(SERVICE)/src/$(FILE)
local_transpile_impl_single: TRANSPILE_DEPENDENCIES= \
		$(patsubst %, --library:$(PROJECT_ROOT)/%/src/Index.dfy, $($(deps_var))) \
		$(patsubst %, --library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX)) \
		--library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
local_transpile_impl_single: transpile_implementation

# Targets to transpile single local service for convenience.
# Specify the local service to build by passing a SERVICE env var.
# Note that this does not generate identical files as `transpile_test_java`,
# and will clobber tests generated by other services.

local_transpile_test_java_single: TARGET=java
local_transpile_test_java_single: OUT=runtimes/java/TestsFromDafny
local_transpile_test_java_single: local_transpile_test_single
	cp -R runtimes/java/TestsFromDafny-java/* runtimes/java/src/test/dafny-generated
	rm -rf runtimes/java/TestsFromDafny-java

local_transpile_test_net_single: TARGET=cs
local_transpile_test_net_single: OUT=runtimes/net/tests/TestsFromDafny
local_transpile_test_net_single: local_transpile_test_single

local_transpile_test_single: TRANSPILE_TARGETS=./dafny/$(SERVICE)/test/$(FILE)
local_transpile_test_single: TRANSPILE_DEPENDENCIES= \
		$(patsubst %, -library:dafny/%/src/Index.dfy, $(PROJECT_SERVICES)) \
		$(patsubst %, -library:$(PROJECT_ROOT)/%, $(PROJECT_INDEX)) \
		-library:$(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
local_transpile_test_single: transpile_test

# Targets to polymorph a single local service for convenience.
# Specify the local service to build by passing a SERVICE env var.

local_polymorph_rust_single: POLYMORPH_LANGUAGE_TARGET=rust
local_polymorph_rust_single: OUTPUT_RUST=--output-rust $(LIBRARY_ROOT)/runtimes/rust
local_polymorph_rust_single: local_polymorph_single

local_polymorph_single: service_deps_var=SERVICE_DEPS_$(SERVICE)
local_polymorph_single: namespace_var=SERVICE_NAMESPACE_$(SERVICE)
local_polymorph_single: PROJECT_DEPENDENCIES=
local_polymorph_single: _polymorph
