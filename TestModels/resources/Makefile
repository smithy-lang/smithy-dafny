# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
PWD := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

polymorph_dafny:
	gradle -p ../../smithy-polymorph run --args="\
	  --output-dafny \
	  --include-dafny $(PWD)/../dafny-dependencies/StandardLibrary/src/Index.dfy \
	  --model $(PWD)/Model \
	  --dependent-model $(PWD)/../dafny-dependencies/Model \
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

clean:
	rm $(PWD)/Model/*.dfy
