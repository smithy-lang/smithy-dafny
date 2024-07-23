// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleTypesTimestampTypes.dfy"
module SimpleTypesTimestampImpl refines AbstractSimpleTypesTimestampOperations {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  predicate GetTimestampEnsuresPublicly(input: GetTimestampInput , output: Result<GetTimestampOutput, Error>)
  {true}



  method GetTimestamp ( config: InternalConfig , input: GetTimestampInput )
    returns (output: Result<GetTimestampOutput, Error>)

  {
    var res := GetTimestampOutput(value := input.value);
    return Success(res);
  }
}
