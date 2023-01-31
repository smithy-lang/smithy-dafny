# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
PWD := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

polymorph_dafny:
	gradle -p ../../smithy-polymorph run --args="\
	  --output-dafny \
      --include-dafny $(PWD)/../dafny-dependencies/StandardLibrary/src/Index.dfy \
      --model $(PWD)/../resources.smithy \
      --dependent-model $(PWD)/../dafny-dependencies/Model \
      --namespace simple.resources";

