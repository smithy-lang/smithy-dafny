// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module Tester {
  import LF = Com.Amazonaws.LakeFormation
  import Types = ComAmazonawsLakeformationTypes
  import opened Wrappers


  method {:test} Harness()
  {
    var client :- expect LF.LakeFormationClient();

    var req: Types.ListResourcesRequest :=
      Types.ListResourcesRequest();
    var resp := client.ListResources(req);

    // The testing role doesn't have permissions yet,
    // so expect this to fail.
    expect resp.Failure?;
  }


}
