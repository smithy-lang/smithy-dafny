# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=10

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleCallingAWSSDKFromLocalService

SERVICE_NAMESPACE_SimpleCallingAWSSDKFromLocalService=simple.callingawssdkfromlocalservice

SERVICE_DEPS_SimpleCallingAWSSDKFromLocalService := \
	aws-sdks/ddb \
	aws-sdks/kms

PROJECT_INDEX := \
	aws-sdks/ddb/src/Index.dfy \
	aws-sdks/kms/src/Index.dfy

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# First, export DAFNY_VERSION=4.2
# Three separate items, because 'make polymorph_code_gen' doesn't quite work
polymorph:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
	make polymorph_dafny
	make polymorph_java
	make polymorph_dotnet
