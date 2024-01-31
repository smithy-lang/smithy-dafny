// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../TestVectors.dfy"

module {:options "-functionSyntax:4"} AllAlgorithmSuites {
  import Types = AwsCryptographyMaterialProvidersTypes
  import AlgorithmSuites
  import HexStrings

  function GetCompatibleCommitmentPolicy(algorithmSuite: Types.AlgorithmSuiteInfo)
    : (commitmentPolicy: Types.CommitmentPolicy)
  {
    match algorithmSuite.id
    case ESDK(_) =>
      if algorithmSuite.commitment.None? then
        Types.CommitmentPolicy.ESDK(Types.ESDKCommitmentPolicy.FORBID_ENCRYPT_ALLOW_DECRYPT)
      else
        Types.CommitmentPolicy.ESDK(Types.ESDKCommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
    case DBE(_) =>
      Types.CommitmentPolicy.DBE(Types.DBECommitmentPolicy.REQUIRE_ENCRYPT_REQUIRE_DECRYPT)
  }

  const ESDKAlgorithmSuites := set id: Types.ESDKAlgorithmSuiteId :: AlgorithmSuites.GetESDKSuite(id)
  const DBEAlgorithmSuites := set id: Types.DBEAlgorithmSuiteId :: AlgorithmSuites.GetDBESuite(id)

  const AllAlgorithmSuites := ESDKAlgorithmSuites + DBEAlgorithmSuites

  lemma AllAlgorithmSuitesIsComplete(id: Types.AlgorithmSuiteId)
    ensures AlgorithmSuites.GetSuite(id) in AllAlgorithmSuites
  {}

  function ToHex(algorithmSuite: Types.AlgorithmSuiteInfo)
    : string
  {
    HexStrings.ToHexString(algorithmSuite.binaryId)
  }

}
