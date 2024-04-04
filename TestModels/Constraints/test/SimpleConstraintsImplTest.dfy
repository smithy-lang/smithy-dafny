// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleConstraintsImpl.dfy"
include "Helpers.dfy"

module SimpleConstraintsImplTest {
    import Helpers
    import SimpleConstraints
    import StandardLibrary.UInt

    import WrappedSimpleConstraintsService
    import opened SimpleConstraintsTypes
    import opened Wrappers
    
    method{:test} TestConstraints(){
        var client :- expect WrappedSimpleConstraintsService.WrappedSimpleConstraints();
        TestGetConstraintWithValidInputs(client);
        TestGetConstraintWithInvalidMyString(client);
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

    method TestGetConstraintWithInvalidMyString(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := GetConstraintsInputTemplate(overrideToInvalidInput := {"myString"});
      var ret := client.GetConstraints(input := input);
      // ret.Failure? in java (good)
      // ret.Success? in dotnet (bad, but we're working on it)
      // importantly -- doesn't raise an exception either way
     }
}
