# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


# These are targets that are shared between all the TestBed projects.
# These targets assume a specific directory structure
# and will only function if executed inside one of these projects.
# Further these targets have some variables
# that are places for the TestBed projects to customize the command line.
# NAMESPACE -- The namespace for the project
# 
# These variables do the same thing,
# but my skils are not capable of taking
# a list of paths and transforming them
# into the required format.
# 
# DEPENDENT-MODELS -- Any dependent models needed for this project
# 	This should take the form `--dependent-model ../path/to/dependent/project/Model`
# LIBRARIES -- The same as DEPENDENT-MODELS but in a different format
# 	This should take the form `-library:../path/to/dependent/project/src/Index.dfy`
# 
# transpile_net_dependencies -- A make target to run any dependent transpile tasks
#  	see transpile_StandardLibrary_net for an example

# This evaluates to the local path _of this file_
TEST_BED_ROOT := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
# This evaluates to the path of the current working directory
PROJECT_ROOT = $(PWD)

########################## Dafny targets

verify:
	dafny \
		-vcsCores:$(CORES) \
		-compile:0 \
		-definiteAssignment:3 \
		-verificationLogger:csv \
		-timeLimit:300 \
		-trace \
		`find . -name '*.dfy'`

dafny-reportgenerator:
	dafny-reportgenerator \
		summarize-csv-results \
		--max-resource-count 10000000 \
		TestResults/*.csv

polymorph_dafny : _polymorph_dafny _polymorph_wrapped_dafny

# For production projects this would be the target to run.
# It is only special cases where the wrapped target
# needs to be added.
_polymorph_dafny :
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(TEST_BED_ROOT)dafny-dependencies/StandardLibrary/src/Index.dfy \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) \
	$(AWS_SDK_CMD)";

_polymorph_wrapped_dafny:
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dafny $(PROJECT_ROOT)/Model \
	--include-dafny $(TEST_BED_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) --output-local-service-test $(PROJECT_ROOT)/Model";


########################## .NET targets

polymorph_net : _polymorph_net _polymorph_wrapped_net

# For production projects each runtime does not need to be broken out.
# The various --output-runtime options can be run togeter.
# They are seperated here to help issolate code for testing.
_polymorph_net:
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dotnet $(PROJECT_ROOT)/runtimes/net/Generated/ \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) \
	$(AWS_SDK_CMD)";

_polymorph_wrapped_net:
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dotnet $(PROJECT_ROOT)/runtimes/net/Generated/Wrapped \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) \
	--output-local-service-test $(PROJECT_ROOT)/Model";

transpile_net: | transpile_implementation_net transpile_test_net transpile_StandardLibrary_net transpile_net_dependencies

transpile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy \
		-library:$(TEST_BED_ROOT)dafny-dependencies/StandardLibrary/src/Index.dfy \
		$(LIBRARIES)

transpile_test_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-useRuntimeLib \
		-out runtimes/net/tests/TestsFromDafny \
		`find ./test -name '*.dfy'` \
		-library:src/Index.dfy

transpile_StandardLibrary_net:
	$(MAKE) -C $(TEST_BED_ROOT)dafny-dependencies/StandardLibrary/ transpile_implementation_net

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/

clean:
	rm -f $(PWD)/Model/*Types.dfy $(PWD)/Model/*TypesWrapped.dfy
	rm -f $(PWD)/runtimes/net/ImplementationFromDafny.cs
	rm -f $(PWD)/runtimes/net/tests/TestFromDafny.cs
	rm -rf $(PWD)/TestResults
	rm -rf $(PWD)/runtimes/net/Generated $(PWD)/runtimes/net/bin $(PWD)/runtimes/net/obj
	rm -rf $(PWD)/runtimes/net/tests/bin $(PWD)/runtimes/net/tests/obj
