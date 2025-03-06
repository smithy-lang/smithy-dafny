# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

ENABLE_EXTERN_PROCESSING=1
CORES=2
USE_DAFNY_STANDARD_LIBRARIES=1

include ../../SharedMakefile.mk

PROJECT_SERVICES := \
    ComAmazonawsS3\

SERVICE_NAMESPACE_ComAmazonawsS3=com.amazonaws.s3
MAX_RESOURCE_COUNT=10000000
AWS_SDK_CMD=--aws-sdk
SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# There is no wrapped target for aws-sdk types
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;
_polymorph_wrapped_python: ;

#Python 
PYTHON_MODULE_NAME=com_amazonaws_s3

TYPES_FILE_PATH=Model/ComAmazonawsS3Types.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"software.amazon.cryptography.services.s3.internaldafny.types\" } ComAmazonawsS3Types"
TYPES_FILE_WITHOUT_EXTERN_STRING="module ComAmazonawsS3Types"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"software.amazon.cryptography.services.s3.internaldafny\" } Com.Amazonaws.S3 refines AbstractComAmazonawsS3Service {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module Com.Amazonaws.S3 refines AbstractComAmazonawsS3Service {"

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr
