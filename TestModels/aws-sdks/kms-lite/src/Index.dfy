// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../model/ComAmazonawsKmsTypes.dfy"

module {:extern "software.amazon.cryptography.services.kms.internaldafny"} Com.Amazonaws.Kms refines AbstractComAmazonawsKmsService {

  function method DefaultKMSClientConfigType() : KMSClientConfigType {
    KMSClientConfigType
  }

}
