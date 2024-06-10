// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleConstraintsImpl.dfy"
include "Helpers.dfy"

module SimpleConstraintsImplTest {
    import Helpers
    import SimpleConstraints
    import StandardLibrary.UInt

    import opened SimpleConstraintsTypes
    import opened Wrappers
    
    method{:test} TestConstraints(){
        var client :- expect SimpleConstraints.SimpleConstraints();
        TestGetConstraintWithValidInputs(client);
        TestGetConstraintWithInvalidMyString(client);
    }

    method TestGetConstraintWithValidInputs(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := Helpers.GetValidInput();
      var ret := client.GetConstraints(input := input);
      expect ret.Success?;
    }

    method TestGetConstraintWithInvalidMyString(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := Helpers.GetValidInput();
      input := input.(MyString := Some(Helpers.ForceMyString("this string is too long")));
      var ret := client.GetConstraints(input := input);
      // This client is NOT wrapped
      // Therefore, it does not do any constraint testing
      expect ret.Success?;
    }
}
