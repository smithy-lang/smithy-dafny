# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
DAFNY_ROOT := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

# Note: This build target fails. polymorph.smithydafny does not support generation for Timestamp types.
polymorph_dafny :
	cd ../../../smithy-polymorph;\
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(DAFNY_ROOT)/../../dafny-dependencies/StandardLibrary/src/Index.dfy \
	--model $(DAFNY_ROOT)/Model \
	--dependent-model $(DAFNY_ROOT)/../../dafny-dependencies/Model \
	--namespace simple.types.timestamp"; \
	./gradlew run --args="\
	--output-dafny \
	--output-local-service-test $(DAFNY_ROOT)/Model \
	--include-dafny $(DAFNY_ROOT)/../../dafny-dependencies/StandardLibrary/src/Index.dfy \
	--model $(DAFNY_ROOT)/Model \
	--dependent-model $(DAFNY_ROOT)/../../dafny-dependencies/Model \
	--namespace simple.types.timestamp"; \

# Note: This build target fails. It generates Dafny code using polymorph.smithydafny, which does not support generation
#       for Timestamp types.
polymorph_net :
	cd ../../../smithy-polymorph;\
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(DAFNY_ROOT)/../../dafny-dependencies/StandardLibrary/src/Index.dfy \
	--output-dotnet $(DAFNY_ROOT)/runtimes/net/Generated/ \
	--model $(DAFNY_ROOT)/Model \
	--dependent-model $(DAFNY_ROOT)/../../dafny-dependencies/Model \
	--namespace simple.types.timestamp"; \
	./gradlew run --args="\
	--output-dafny \
	--output-local-service-test $(DAFNY_ROOT)/Model \
	--include-dafny $(DAFNY_ROOT)/../../dafny-dependencies/StandardLibrary/src/Index.dfy \
	--output-dotnet $(DAFNY_ROOT)/runtimes/net/Generated/Wrapped \
	--model $(DAFNY_ROOT)/Model \
	--dependent-model $(DAFNY_ROOT)/../../dafny-dependencies/Model \
	--namespace simple.types.timestamp"; \

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

transpile_net: | transpile_implementation_net transpile_test_net transpile_net_dependencies

transpile_implementation_net:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:cs \
		-spillTargetCode:3 \
		-runAllTests:1 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-useRuntimeLib \
		-out runtimes/net/ImplementationFromDafny \
		./src/Index.dfy \
		-library:../../dafny-dependencies/StandardLibrary/src/Index.dfy \


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

transpile_net_dependencies:
	$(MAKE) -C ../../dafny-dependencies/StandardLibrary transpile_implementation_net \

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/
	