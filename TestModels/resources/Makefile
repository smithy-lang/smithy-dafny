# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
PWD := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

polymorph_dafny:
	gradle -p ../../smithy-polymorph run --args="\
	  --output-dafny \
	  --include-dafny $(PWD)../dafny-dependencies/StandardLibrary/src/Index.dfy \
	  --model $(PWD)Model \
	  --dependent-model $(PWD)../dafny-dependencies/Model \
	  --namespace simple.resources";
	# gradle -p ../../smithy-polymorph run --args="\
	#   --output-dafny \
	#   --output-local-service-test $(PWD)/Model \
	#   --include-dafny $(PWD)/../dafny-dependencies/StandardLibrary/src/Index.dfy \
	#   --model $(PWD)/Model \
	#   --dependent-model $(PWD)/../dafny-dependencies/Model \
	#   --namespace simple.resources";

verify:
	dafny \
	  -vcsCores:$(CORES) \
	  -compile:0 \
	  -definiteAssignment:3 \
	  -verificationLogger:csv \
	  -timeLimit:300 \
	  -trace \
	  `find . -name '*.dfy'`

polymorph_net:
	gradle -p ../../smithy-polymorph run --args="\
	  --output-dotnet $(PWD)runtimes/net/Generated/ \
	  --include-dafny $(PWD)../dafny-dependencies/StandardLibrary/src/Index.dfy \
	  --model $(PWD)Model \
	  --dependent-model $(PWD)../dafny-dependencies/Model \
	  --namespace simple.resources";

transpile_net: | transpile_implementation_net transpile_net_dependencies

transpile_implementation_net:
	dafny \
	  -vcsCores:$(CORES) \
	  -compileTarget:cs \
	  -spillTargetCode:3 \
	  -compile:0 \
	  -optimizeErasableDatatypeWrapper:0 \
	  -useRuntimeLib \
	  -out runtimes/net/ImplementationFromDafny \
	  -library $(PWD)../dafny-dependencies/StandardLibrary/src/Index.dfy \
	  ./src/Index.dfy

transpile_net_dependencies:
	$(MAKE) -C $(PWD)../dafny-dependencies/StandardLibrary/ transpile_implementation_net

setup_net:
	dotnet restore runtimes/net/

clean:
	rm $(PWD)Model/*.dfy $(PWD)runtimes/net/ImplementationFromDafny.cs;
	rm -rf $(PWD)TestResults $(PWD)runtimes/net/Generated
