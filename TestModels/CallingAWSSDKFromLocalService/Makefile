# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2
TRANSPILE_TESTS_IN_RUST=1

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleCallingawssdkfromlocalservice

MAIN_SERVICE_FOR_RUST := SimpleCallingawssdkfromlocalservice

PROJECT_DEPENDENCIES := \
	aws-sdks/kmsv2 \
	aws-sdks/ddbv2 

PROJECT_INDEX := \
	aws-sdks/kmsv2/src/Index.dfy \
	aws-sdks/ddbv2/src/Index.dfy

SERVICE_NAMESPACE_SimpleCallingawssdkfromlocalservice=simple.callingawssdkfromlocalservice

SERVICE_DEPS_SimpleCallingawssdkfromlocalservice := \
	aws-sdks/kmsv2 \
	aws-sdks/ddbv2

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleCallingawssdkfromlocalserviceTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny.types\" } SimpleCallingawssdkfromlocalserviceTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleCallingawssdkfromlocalserviceTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny\" } SimpleCallingawssdkfromlocalservice refines AbstractSimpleCallingawssdkfromlocalserviceService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleCallingawssdkfromlocalservice refines AbstractSimpleCallingawssdkfromlocalserviceService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleCallingawssdkfromlocalserviceImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny.wrapped\"} WrappedSimpleCallingawssdkfromlocalserviceService refines WrappedAbstractSimpleCallingawssdkfromlocalserviceService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleCallingawssdkfromlocalserviceService refines WrappedAbstractSimpleCallingawssdkfromlocalserviceService {"

# Go

GO_DEPENDENCY_MODULE_NAMES := \
	--go-dependency-module-name=com.amazonaws.kms=github.com/smithy-lang/smithy-dafny/kmsv2 \
	--go-dependency-module-name=com.amazonaws.dynamodb=github.com/smithy-lang/smithy-dafny/ddbv2 \
	--go-dependency-module-name=sdk.com.amazonaws.dynamodb=github.com/aws/aws-sdk-go-v2/service/dynamodb \
	--go-dependency-module-name=sdk.com.amazonaws.kms=github.com/aws/aws-sdk-go-v2/service/kms

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService"

TRANSLATION_RECORD_GO := \
	dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
	aws-sdks/kmsv2/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr \
	aws-sdks/ddbv2/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr 
	