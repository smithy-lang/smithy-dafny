// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimplePositionalTypes.dfy"

module SimpleResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimplePositionalTypes

  class SimpleResource extends Types.ISimpleResource
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    const name: string

    constructor (
      name: string
    )
      ensures this.name == name
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      this.name := name;

      History := new Types.ISimpleResourceCallHistory();
      Modifies := {History};
    }

    predicate GetNameEnsuresPublicly(
      input: Types.GetNameInput,
      output: Result<Types.GetNameOutput, Types.Error>
    ) {true}

    method GetName'(
      input: Types.GetNameInput
    ) returns (
        output: Result<Types.GetNameOutput, Types.Error>
      )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures && ValidState()
      ensures GetNameEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      return Success(Types.GetNameOutput(name := name));
    }
  }
}
