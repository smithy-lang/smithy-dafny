// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../model/ComAmazonawsSqsTypes.dfy"

module {:extern "software.amazon.cryptography.services.sqs.internaldafny"} Com.Amazonaws.Sqs refines AbstractComAmazonawsSqsService {

  function method DefaultSQSClientConfigType() : SQSClientConfigType {
    SQSClientConfigType
  }

}
