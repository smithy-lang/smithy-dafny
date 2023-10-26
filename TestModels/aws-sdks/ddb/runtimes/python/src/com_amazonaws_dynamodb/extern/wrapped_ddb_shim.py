# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import software_amazon_cryptography_services_dynamodb_internaldafny
from com_amazonaws_dynamodb.smithygenerated.shim import DynamoDB_20120810Shim
import Wrappers
import boto3

TEST_REGION = "us-west-2"

@staticmethod
def WrappedDdbClient(region=None):
    if region is not None:
        boto_config = Config(
            region_name=region
        )
        impl = boto3.client("dynamodb", config=boto_config)
    else:
        impl = boto3.client("dynamodb", region_name=TEST_REGION)
        region = boto3.session.Session().region_name
    wrapped_client = DynamoDB_20120810Shim(impl, region)
    return Wrappers.Result_Success(wrapped_client)

software_amazon_cryptography_services_dynamodb_internaldafny.default__.DynamoDBClient = WrappedDdbClient
software_amazon_cryptography_services_dynamodb_internaldafny.DynamoDBClient = WrappedDdbClient