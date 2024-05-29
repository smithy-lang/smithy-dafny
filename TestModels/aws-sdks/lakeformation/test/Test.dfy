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

    // Just expecting that the request is successful.
    var ret :- expect client.ListResources(req);
  }


}
