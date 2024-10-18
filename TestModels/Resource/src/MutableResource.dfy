// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"

module MutableResource {
  import opened StandardLibrary
  import Wrappers
  import Types = SimpleResourcesTypes

  // The default export set
  export
    // Revealing a class will reveal constructor and extends
    reveals
      MutableResource
    provides
      // Because `extends Types.IMutableResource` is revealed
      // all the things that need to be implement from the trait
      // need to be visible..
      // These are provided so that the spec is not visible.
      MutableResource.GetMutableResourceData',
      MutableResource.ValidState,
      MutableResource.InternalValidState,
      MutableResource.GetMutableResourceDataEnsuresPublicly,
      // These are values that need to be visible
      // because they are in the spec of the constructor.
      MutableResource.value,
      MutableResource.name,
      // Need to provide the dependent modules
      Types,
      Wrappers

  // This is for testing
  export ForTesting reveals *

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
    const value: Wrappers.Option<string>

    // Some internal state that we modify!
    var MyInternalState: nat

    constructor (
      value: Wrappers.Option<string>,
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

    predicate GetMutableResourceDataEnsuresPublicly(
      input: Types.GetMutableResourceDataInput,
      output: Wrappers.Result<Types.GetMutableResourceDataOutput, Types.Error>
    ) {true}

    method GetMutableResourceData'(
      input: Types.GetMutableResourceDataInput
    ) returns (
        output: Wrappers.Result<Types.GetMutableResourceDataOutput, Types.Error>
      )
      requires
        && InternalValidState()
      modifies InternalModifies
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases InternalModifies
      ensures
        && InternalValidState()
      ensures GetMutableResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)
    {

      // Yes, we can indeed modify our state!
      MyInternalState := MyInternalState + 1;

      var rtnString: string := if input.stringValue.Some? then
        this.name + " " + input.stringValue.value
      else
        this.name;
      var rtn: Types.GetMutableResourceDataOutput := Types.GetMutableResourceDataOutput(
        blobValue := input.blobValue,
        booleanValue := input.booleanValue,
        stringValue := Wrappers.Some(rtnString),
        integerValue := input.integerValue,
        longValue := input.longValue
      );
      return Wrappers.Success(rtn);
    }
  }
}
