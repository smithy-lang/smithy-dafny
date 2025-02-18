// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleConstraintsTypes.dfy"

module SimpleConstraintsImpl refines AbstractSimpleConstraintsOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate GetConstraintsEnsuresPublicly(input: GetConstraintsInput, output: Result<GetConstraintsOutput, Error>) {
    true
  }
  method GetConstraints ( config: InternalConfig,  input: GetConstraintsInput )
    returns (output: Result<GetConstraintsOutput, Error>)
  {  
    var res := GetConstraintsOutput(
      MyString := input.MyString,
      NonEmptyString := input.NonEmptyString,
      StringLessThanOrEqualToTen := input.StringLessThanOrEqualToTen,
      MyBlob := input.MyBlob,
      NonEmptyBlob := input.NonEmptyBlob,
      BlobLessThanOrEqualToTen := input.BlobLessThanOrEqualToTen,
      MyList := input.MyList,
      NonEmptyList := input.NonEmptyList,
      ListLessThanOrEqualToTen := input.ListLessThanOrEqualToTen,
      ListWithConstraint := input.ListWithConstraint,
      MyMap := input.MyMap,
      NonEmptyMap := input.NonEmptyMap,
      MapLessThanOrEqualToTen := input.MapLessThanOrEqualToTen,
      MapWithConstraint := input.MapWithConstraint,
      // Alphabetic := input.Alphabetic,
      OneToTen := input.OneToTen,
      GreaterThanOne := input.GreaterThanOne,
      LessThanTen := input.LessThanTen,
      // MyUniqueList := input.MyUniqueList,
      // MyComplexUniqueList := input.MyComplexUniqueList,
      MyUtf8Bytes := input.MyUtf8Bytes,
      MyListOfUtf8Bytes := input.MyListOfUtf8Bytes,
      UnionWithConstraint := input.UnionWithConstraint,
      ComplexStructureList := input.ComplexStructureList
    );

    return Success(res);
  }
}
