// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/ComAmazonawsSqsTypes.dfy"

module {:options "--function-syntax:4"}{:extern "software.amazon.cryptography.services.sqs.internaldafny"} Com.Amazonaws.SQS refines AbstractComAmazonawsSqsService {

  function DefaultSQSClientConfigType() : SQSClientConfigType {
    SQSClientConfigType
  }

}
