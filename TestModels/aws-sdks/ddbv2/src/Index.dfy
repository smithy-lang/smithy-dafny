// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsDynamodbTypes.dfy"

module {:extern "software.amazon.cryptography.services.dynamodb.internaldafny"} Com.Amazonaws.Dynamodb refines AbstractComAmazonawsDynamodbService {

  function method DefaultDynamoDBClientConfigType() : DynamoDBClientConfigType {
    DynamoDBClientConfigType
  }

}
