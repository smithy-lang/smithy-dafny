// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"

module SimpleResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimpleResourcesTypes    

  class SimpleResource extends Types.ISimpleResource
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }
    
    const name: string
    const value: Option<string>

    constructor (
      value: Option<string>,
      name: string
    )
      requires |name| > 0
      ensures this.value == value
      ensures this.name == name
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
      this.value := value;
      this.name := name;

      History := new Types.ISimpleResourceCallHistory();
      Modifies := {History};
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
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures && ValidState()
      ensures GetResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
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
