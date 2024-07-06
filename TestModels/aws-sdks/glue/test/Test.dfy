// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module Tester {
  import Glue = Com.Amazonaws.Glue
  import Types = ComAmazonawsGlueTypes
  import opened Wrappers


  method {:test} Harness()
  {
    var client :- expect Glue.GlueClient();

    var req: Glue.Types.GetDatabaseRequest :=
      Glue.Types.GetDatabaseRequest(Name := "foo");
    var resp := client.GetDatabase(req);
    
    // The testing role doesn't have permissions yet,
    // so expect this to fail.
    expect resp.Failure?;
  }


}
