# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import software_amazon_cryptography_services_kms_internaldafny
from com_amazonaws_kms.smithygenerated.shim import TrentServiceShim
import Wrappers
import boto3

@staticmethod
def WrappedTrentService():
    # wrapped_config = dafny_config_to_smithy_config(config)
    impl = boto3.client("kms")
    wrapped_client = TrentServiceShim(impl)
    return Wrappers.Result_Success(wrapped_client)

software_amazon_cryptography_services_kms_internaldafny.default__.KMSClient = WrappedTrentService
software_amazon_cryptography_services_kms_internaldafny.TrentServiceClient = WrappedTrentService