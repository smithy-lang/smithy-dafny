DAFNY_ROOT := $(shell pwd)

polymorph_dafny :
	cd ../../../smithy-polymorph;\
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(DAFNY_ROOT)/../../DafnyLib/std/src/Index.dfy \
	--model $(DAFNY_ROOT)/Model \
	--namespace simple.types.boolean"; \
	./gradlew run --args="\
	--output-dafny $(DAFNY_ROOT)/Model \
	--include-dafny $(DAFNY_ROOT)/../../DafnyLib/std/src/Index.dfy \
	--model $(DAFNY_ROOT)/Model \
	--namespace simple.types.boolean --wrapped-local-service"; \

polymorph_net :
	cd ../../../smithy-polymorph;\
	./gradlew run --args="\
	--output-dafny \
	--include-dafny $(DAFNY_ROOT)/../../DafnyLib/std/src/Index.dfy \
	--output-dotnet $(DAFNY_ROOT)/runtimes/net/Generated/ \
	--model $(DAFNY_ROOT)/Model \
	--namespace simple.types.boolean"; \
	./gradlew run --args="\
	--output-dafny $(DAFNY_ROOT)/Model \
	--include-dafny $(DAFNY_ROOT)/../../DafnyLib/std/src/Index.dfy \
	--output-dotnet $(DAFNY_ROOT)/runtimes/net/Generated/Wrapped \
	--model $(DAFNY_ROOT)/Model \
	--namespace simple.types.boolean --wrapped-local-service"; \

	# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

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
		-library:../../DafnyLib/std/src/Index.dfy


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
	$(MAKE) -C ../../DafnyLib/std transpile_implementation_net

test_net:
	dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

test_net_mac_intel:
	DYLD_LIBRARY_PATH="/usr/local/opt/openssl@1.1/lib" dotnet run \
		--project runtimes/net/tests/ \
		--framework net6.0

setup_net:
	dotnet restore runtimes/net/
	