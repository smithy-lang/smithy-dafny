# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.dynamodb
AWS_SDK_CMD=--aws-sdk

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=

# There is no wrapped target for aws-sdk types
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;

format_net:
	pushd runtimes/net && dotnet format && popd
