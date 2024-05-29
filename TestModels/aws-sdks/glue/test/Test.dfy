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
    print resp;
  }


}
