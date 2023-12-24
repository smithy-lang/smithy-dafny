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

# On macOS, sed requires an extra parameter of ""
OS := $(shell uname)
ifeq ($(OS), Darwin)
  SED_PARAMETER := ""
else
  SED_PARAMETER :=
endif

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
        $(COMPILE_SUFFIX_OPTION) \
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
		$(COMPILE_SUFFIX_OPTION) \
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
	$(OUTPUT_DAFNY) \
	$(OUTPUT_DOTNET) \
	$(OUTPUT_JAVA) \
    $(OUTPUT_PYTHON) \
    $(POLYMORPH_PYTHON_MODULE_NAME) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(AWS_SDK_CMD)";

_polymorph_wrapped:
	@: $(if ${CODEGEN_CLI_ROOT},,$(error You must pass the path CODEGEN_CLI_ROOT: CODEGEN_CLI_ROOT=/path/to/smithy-dafny/codegen/smithy-dafny-codegen-cli));
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	$(DAFNY_VERSION_OPTION) \
	$(OUTPUT_DAFNY_WRAPPED) \
	$(OUTPUT_DOTNET_WRAPPED) \
	$(OUTPUT_JAVA_WRAPPED) \
	$(OUTPUT_PYTHON_WRAPPED) \
    $(POLYMORPH_PYTHON_MODULE_NAME) \
	--model $(if $(DIR_STRUCTURE_V2),$(LIBRARY_ROOT)/dafny/$(SERVICE)/Model,$(LIBRARY_ROOT)/Model) \
	--dependent-model $(PROJECT_ROOT)/$(SMITHY_DEPS) \
	$(patsubst %, --dependent-model $(PROJECT_ROOT)/%/Model, $($(service_deps_var))) \
	--namespace $($(namespace_var)) \
	$(OUTPUT_LOCAL_SERVICE) \
	$(AWS_SDK_CMD)";

_polymorph_dependencies:
	@$(foreach dependency, \
		$(PROJECT_DEPENDENCIES), \
		$(MAKE) -C $(PROJECT_ROOT)/$(dependency) polymorph_$(POLYMORPH_LANGUAGE_TARGET); \
	)

# Generates all target runtime code for all namespaces in this project.
.PHONY: polymorph_code_gen
polymorph_code_gen:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_code_gen || exit 1; \
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
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny || exit 1; \
	done

_polymorph_dafny: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
	--include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_dafny: _polymorph
_polymorph_dafny: OUTPUT_DAFNY_WRAPPED=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
    --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy
_polymorph_dafny: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_dafny: _polymorph_wrapped
_polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
_polymorph_dafny: _polymorph_dependencies

# Generates dotnet code for all namespaces in this project
.PHONY: polymorph_net
polymorph_net:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_net || exit 1; \
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
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_java || exit 1; \
	done

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph
_polymorph_java: OUTPUT_JAVA_WRAPPED=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_java: _polymorph_wrapped
_polymorph_java: POLYMORPH_LANGUAGE_TARGET=java
_polymorph_java: _polymorph_dependencies

.PHONY: polymorph_python
polymorph_python:
	for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_python || exit 1; \
	done

_polymorph_python: OUTPUT_PYTHON=--output-python $(LIBRARY_ROOT)/runtimes/python/smithygenerated
_polymorph_python: POLYMORPH_PYTHON_MODULE_NAME=--python-module-name $(PYTHON_MODULE_NAME)
_polymorph_python: _polymorph
# TODO-Python: Right now, wrapped code generation requires an isolated directory,
#   as it runs `rm models.py` and `rm errors.py` after generating.
# Work is planned to not do this by writing a SymbolVisitor specific to wrapped localService generation.
# This will resolve some of the weirdness in this section.
_polymorph_python: OUTPUT_PYTHON_WRAPPED=--output-python $(LIBRARY_ROOT)/runtimes/python/smithygenerated_wrapped
_polymorph_python: OUTPUT_LOCAL_SERVICE=--local-service-test
_polymorph_python: _polymorph_wrapped
_polymorph_python:
	rm -rf runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	mkdir -p runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	cp -r runtimes/python/smithygenerated_wrapped/* runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	cp -r runtimes/python/smithygenerated/* runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	rm runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated/README.md
	rm runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated/pyproject.toml
	rm -rf runtimes/python/smithygenerated
	rm -rf runtimes/python/smithygenerated_wrapped
_polymorph_python: POLYMORPH_LANGUAGE_TARGET=python
_polymorph_python: _polymorph_dependencies

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

transpile_java: transpile_java mvn_local_deploy_dependencies
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

########################## Python targets

transpile_python: _python_underscore_dependency_extern_names
transpile_python: _python_underscore_extern_names
transpile_python: transpile_implementation_python
transpile_python: transpile_test_python
transpile_python: transpile_dependencies_python
transpile_python: _python_revert_underscore_extern_names
transpile_python: _python_revert_underscore_dependency_extern_names
transpile_python: _mv_internaldafny_python
transpile_python: _remove_src_module_python
transpile_python: _rename_test_main_python

transpile_implementation_python: TARGET=py
transpile_implementation_python: OUT=runtimes/python/dafny_src
transpile_implementation_python: COMPILE_SUFFIX_OPTION=
transpile_implementation_python: _transpile_implementation_all
transpile_implementation_python: transpile_dependencies_python
transpile_implementation_python: transpile_src_python
transpile_implementation_python: transpile_test_python
transpile_implementation_python: _mv_internaldafny_python
transpile_implementation_python: _remove_src_module_python

transpile_src_python: TARGET=py
transpile_src_python: OUT=runtimes/python/dafny_src
transpile_src_python: COMPILE_SUFFIX_OPTION=
transpile_src_python: _transpile_implementation_all

transpile_test_python: TARGET=py
transpile_test_python: OUT=runtimes/python/__main__
transpile_test_python: COMPILE_SUFFIX_OPTION=
transpile_test_python: _transpile_test_all

# Hacky workaround until Dafny supports per-language extern names.
# Replaces `.`s with `_`s in strings like `{:extern ".*"}`.
# This is flawed logic and should be removed, but is a reasonable band-aid for now.
# TODO-Python BLOCKING: Once Dafny supports per-language extern names, remove and replace with Pythonic extern names.
# This is tracked in https://github.com/dafny-lang/dafny/issues/4322.
# This may require new Smithy-Dafny logic to generate Pythonic extern names.
_python_underscore_extern_names:
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\".*/s/\./_/g' {} \;
	find Model -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\.*"/s/\./_/g' {} \;
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\".*/s/\./_/g' {} \;

_python_underscore_dependency_extern_names:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) _python_underscore_extern_names
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _python_underscore_extern_names;, $(LIBRARIES))

_python_revert_underscore_extern_names:
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\".*/s/_/\./g' {} \;
	find Model -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\".*/s/_/\./g' {} \; 2>/dev/null
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/.*{:extern \".*\".*/s/_/\./g' {} \;

_python_revert_underscore_dependency_extern_names:
	$(MAKE) -C $(STANDARD_LIBRARY_PATH) _python_revert_underscore_extern_names
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _python_revert_underscore_extern_names;, $(LIBRARIES))

# Move Dafny-generated code into its expected location in the Python module
_mv_internaldafny_python:
	# Remove any previously generated Dafny code in src/, then copy in newly-generated code
	rm -rf runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/
	mkdir -p runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/
	mv runtimes/python/dafny_src-py/*.py runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated
	rm -rf runtimes/python/dafny_src-py
	# Remove any previously generated Dafny code in test/, then copy in newly-generated code
	rm -rf runtimes/python/test/internaldafny/generated
	mkdir -p runtimes/python/test/internaldafny/generated
	mv runtimes/python/__main__-py/*.py runtimes/python/test/internaldafny/generated
	rm -rf runtimes/python/__main__-py

# Versions of Dafny as of ~9/28 seem to ALWAYS write output to __main__.py,
#   regardless of the OUT parameter...?
# We should figure out what happened and get a workaround
# For now, always write OUT to __main__, then manually rename the primary file...
# TODO-Python BLOCKING: Resolve this before releasing libraries
# Note the name internaldafny_test_executor is specifically chosen
# so as to not be picked up by pytest,
# which finds test_*.py or *_test.py files.
# This is neither, and will not be picked up by pytest.
# This file SHOULD not be run from a context that has not imported the wrapping shim,
#   otherwise the tests will fail.
# We write an extern which WILL be picked up by pytest.
# This extern will import the wrapping shim, then import this `internaldafny_test_executor` to run the tests.
_rename_test_main_python:
	mv runtimes/python/test/internaldafny/generated/__main__.py runtimes/python/test/internaldafny/generated/internaldafny_test_executor.py

_remove_src_module_python:
	# Remove the src/ `module_.py` file.
	# There is a race condition between the src/ and test/ installation of this file.
	# The file that is installed least recently is overwritten by the file installed most recently.
	# The test/ file contains code to execute tests. The src/ file is largely empty.
	# If the src/ file is installed most recently, tests will fail to run.
	# By removing the src/ file, we ensure the test/ file is always the installed file.
	rm runtimes/python/src/$(PYTHON_MODULE_NAME)/internaldafny/generated/module_.py

transpile_dependencies_python: LANG=python
transpile_dependencies_python: transpile_dependencies

test_python:
	rm -rf runtimes/python/.tox
	tox -c runtimes/python --verbose

########################## Clean targets (for all languages)

clean: _clean

_clean:
	rm -f $(LIBRARY_ROOT)/Model/*Types.dfy $(LIBRARY_ROOT)/Model/*TypesWrapped.dfy
	rm -f $(LIBRARY_ROOT)/runtimes/net/ImplementationFromDafny.cs
	rm -f $(LIBRARY_ROOT)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(LIBRARY_ROOT)/TestResults
	rm -rf $(LIBRARY_ROOT)/runtimes/net/Generated $(LIBRARY_ROOT)/runtimes/net/bin $(LIBRARY_ROOT)/runtimes/net/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/net/tests/bin $(LIBRARY_ROOT)/runtimes/net/tests/obj
	rm -rf $(LIBRARY_ROOT)/runtimes/python/src/**/internaldafny/generated
	rm -rf $(LIBRARY_ROOT)/runtimes/python/src/**/smithygenerated
	rm -rf $(LIBRARY_ROOT)/runtimes/python/test/internaldafny/generated
	rm -rf $(LIBRARY_ROOT)/runtimes/python/.tox
	rm -rf $(LIBRARY_ROOT)/runtimes/python/poetry.lock
	rm -rf $(LIBRARY_ROOT)/runtimes/python/build