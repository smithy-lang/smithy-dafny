// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "Helpers.dfy"

module SimpleConstraintsImplTest {
    import Helpers
    import SimpleConstraints
    import StandardLibrary.UInt

    import opened SimpleConstraintsTypes
    import opened Wrappers
    
    method {:test} TestConstraints() {
        var client :- expect SimpleConstraints.SimpleConstraints();
        TestGetConstraintWithValidInputs(client);
        // TestGetConstraintWithInvalidMyString(client);
        TestGetConstraintWithInvalidLessThanTen(client);
    }

    // method TestGetConstraintWithInvalidMyString(client: ISimpleConstraintsClient)
    //   requires client.ValidState()
    //   modifies client.Modifies
    //   ensures client.ValidState()
    // {
    //   var input := Helpers.GetConstraintsInputTemplate(overrideToInvalidInput := {"myString"});
    //   var ret := client.GetConstraints(input := input);
    //   print ret,"\n";
    //   expect ret.Failure?;
    // }

    method TestGetConstraintWithInvalidLessThanTen(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := Helpers.GetConstraintsInputTemplate(overrideToInvalidInput := {"lessThanTen"});
      var ret := client.GetConstraints(input := input);
      print ret,"\n";
      expect ret.Failure?;
    }

    method TestGetConstraintWithValidInputs(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := Helpers.GetConstraintsInputTemplate();
      var ret := client.GetConstraints(input := input);
      expect ret.Success?;
    }

}
