// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../model/ComAmazonawsLakeformationTypes.dfy"

module {:options "--function-syntax:4"}{:extern "software.amazon.cryptography.services.lakeformation.internaldafny"} Com.Amazonaws.LakeFormation refines AbstractComAmazonawsLakeformationService {

  function DefaultLakeFormationClientConfigType() : LakeFormationClientConfigType {
    LakeFormationClientConfigType
  }

}
