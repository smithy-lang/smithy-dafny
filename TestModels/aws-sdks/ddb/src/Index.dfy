// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsDynamodbTypes.dfy"

module {:extern "software_amazon_cryptography_services_dynamodb_internaldafny"} Com_Amazonaws_Dynamodb refines AbstractComAmazonawsDynamodbService {

  function method DefaultDynamoDBClientConfigType() : DynamoDBClientConfigType {
    DynamoDBClientConfigType
  }

}
