# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleCallingAWSSDKFromLocalService

SERVICE_NAMESPACE_SimpleCallingAWSSDKFromLocalService=simple.callingawssdkfromlocalservice

SERVICE_DEPS_SimpleCallingAWSSDKFromLocalService :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# First, export DAFNY_VERSION=4.2
# Three separate items, because 'make polymorph_code_gen' doesn't quite work
polymorph:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
	make polymorph_dafny
	make polymorph_java
	make polymorph_dotnet
