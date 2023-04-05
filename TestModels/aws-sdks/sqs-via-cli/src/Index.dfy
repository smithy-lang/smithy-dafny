// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsSqsTypes.dfy"

module {:extern "Dafny.Com.Amazonaws.Sqs"} Com.Amazonaws.Sqs refines AbstractComAmazonawsSqsService {

  function method DefaultSQSClientConfigType() : SQSClientConfigType {
    SQSClientConfigType
  }

}