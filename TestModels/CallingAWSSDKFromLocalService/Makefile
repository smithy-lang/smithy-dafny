# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=10

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleCallingAWSSDKFromLocalService

PROJECT_DEPENDENCIES := \
	aws-sdks/ddb \
	aws-sdks/kms 

PROJECT_INDEX := \
	aws-sdks/ddb/src/Index.dfy \
	aws-sdks/kms/src/Index.dfy

SERVICE_NAMESPACE_SimpleCallingAWSSDKFromLocalService=simple.callingawssdkfromlocalservice

SERVICE_DEPS_SimpleCallingAWSSDKFromLocalService := \
	aws-sdks/ddb \
	aws-sdks/kms

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy