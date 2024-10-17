// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"

module MutableResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimpleResourcesTypes

  class MutableResource extends Types.IMutableResource
    {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies && this in Modifies
    {
      && History in Modifies
      && this in Modifies
    }

    predicate InternalValidState()
      reads this`InternalModifies, InternalModifies
      ensures InternalValidState() ==> History !in InternalModifies
    {
      && History !in InternalModifies
      && this in InternalModifies
    }

    const name: string
    const value: Option<string>

    // Some internal state that we modify!
    var MyInternalState: nat

    constructor (
      value: Option<string>,
      name: string
    )
      requires |name| > 0
      ensures this.value == value
      ensures this.name == name
      ensures ValidState() && fresh(History) && fresh(Modifies)
      ensures InternalValidState()
    {
      this.value := value;
      this.name := name;
      MyInternalState := 0;

      History := new Types.IMutableResourceCallHistory();
      Modifies := {History, this};
      InternalModifies := {this};

    }

    predicate GetResourceDataEnsuresPublicly(
      input: Types.GetResourceDataInput,
      output: Result<Types.GetResourceDataOutput, Types.Error>
    ) {true}

    method GetResourceData'(
      input: Types.GetResourceDataInput
    ) returns (
        output: Result<Types.GetResourceDataOutput, Types.Error>
      )
      requires
        && InternalValidState()
      modifies InternalModifies
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases InternalModifies
      ensures
        && InternalValidState()
      ensures GetResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)
    {

      // Yes, we can indeed modify our state!
      MyInternalState := MyInternalState + 1;

      var rtnString: string := if input.stringValue.Some? then
        this.name + " " + input.stringValue.value
      else
        this.name;
      var rtn: Types.GetResourceDataOutput := Types.GetResourceDataOutput(
        blobValue := input.blobValue,
        booleanValue := input.booleanValue,
        stringValue := Some(rtnString),
        integerValue := input.integerValue,
        longValue := input.longValue
      );
      return Success(rtn);
    }
  }
}
