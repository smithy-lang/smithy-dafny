# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=10

ENABLE_EXTERN_PROCESSING=1

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

# Python

PYTHON_MODULE_NAME=simple_callingawssdkfromlocalservice

PYTHON_DEPENDENCY_MODULE_NAMES := \
	--dependency-library-name=com.amazonaws.dynamodb=com_amazonaws_dynamodb \
	--dependency-library-name=com.amazonaws.kms=com_amazonaws_kms

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../aws-sdks/ddb/runtimes/python/src/com_amazonaws_dynamodb/internaldafny/generated/dafny_src-py.dtr \
    --translation-record ../aws-sdks/kms/runtimes/python/src/com_amazonaws_kms/internaldafny/generated/dafny_src-py.dtr

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleCallingawssdkfromlocalserviceTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny.types\" } SimpleCallingawssdkfromlocalserviceTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleCallingawssdkfromlocalserviceTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny\" } SimpleCallingAWSSDKFromLocalService refines AbstractSimpleCallingawssdkfromlocalserviceService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleCallingAWSSDKFromLocalService refines AbstractSimpleCallingawssdkfromlocalserviceService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.callingawssdkfromlocalservice.internaldafny.wrapped\"} WrappedSimpleCallingAWSSDKFromLocalServiceService refines WrappedAbstractSimpleCallingawssdkfromlocalserviceService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleCallingAWSSDKFromLocalServiceService refines WrappedAbstractSimpleCallingawssdkfromlocalserviceService {"

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService"

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr