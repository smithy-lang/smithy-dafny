# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.dynamodb

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=
transpile_net_dependencies: ;

_polymorph_dafny :
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dafny $(PROJECT_ROOT)/Model \
	--include-dafny $(TEST_BED_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) --aws-sdk";

_polymorph_net:
	cd $(TEST_BED_ROOT)../smithy-polymorph; \
	./gradlew run --args="\
	--output-dotnet $(PROJECT_ROOT)/runtimes/net/Generated/ \
	--model $(PROJECT_ROOT)/Model \
	--dependent-model $(TEST_BED_ROOT)/dafny-dependencies/Model \
	$(DEPENDENT-MODELS) \
	--namespace $(NAMESPACE) --aws-sdk";

# There is no wrapped target for aws-sdk types
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;