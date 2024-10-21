// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypes.dfy"

module ExtendableResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimpleExtendableResourcesTypes

  const DEFAULT_RESOURCE_NAME := "dafny-default";
  
  class OpaqueMessage {
    // See the comments in `CheckOpaqueError` of `../test/Helpers.dfy` for 
    // an explanation of why OpaqueMessage will not survive translation.
    const message: string := "Hard Coded Opaque Message that will not survive translation.";
    constructor () {}
  }

  class ExtendableResource extends Types.IExtendableResource
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
      ensures ValidState() ==> |this.name| > 0
    {
      && History in Modifies
      && |this.name| > 0
    }

    const name: string
    
    constructor ()
      ensures ValidState() && fresh(History) && fresh(Modifies)
      ensures this.name == DEFAULT_RESOURCE_NAME
    {
      this.name := DEFAULT_RESOURCE_NAME;
      History := new Types.IExtendableResourceCallHistory();
      Modifies := {History};
    }

    constructor OfName(name: string)
      requires |name| > 0
      ensures ValidState() && fresh(History) && fresh(Modifies)
      ensures this.name == name
    {
      this.name := name;
      History := new Types.IExtendableResourceCallHistory();
      Modifies := {History};
    }

    predicate AlwaysMultipleErrorsEnsuresPublicly(
      input: Types.GetExtendableResourceErrorsInput,
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    ) {true}

    method AlwaysMultipleErrors'(
      input: Types.GetExtendableResourceErrorsInput
    ) returns (
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures AlwaysMultipleErrorsEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      var nestedError: Types.Error := Types.SimpleExtendableResourcesException(
        message := "Hard Coded Modeled Exception in Collection"
      );
      return Failure(Types.CollectionOfErrors([nestedError], message := "Something"));
    }

    predicate GetExtendableResourceDataEnsuresPublicly(
      input: Types.GetExtendableResourceDataInput,
      output: Result<Types.GetExtendableResourceDataOutput, Types.Error>
    ) {true}

    method GetExtendableResourceData'(
      input: Types.GetExtendableResourceDataInput
    ) returns (
      output: Result<Types.GetExtendableResourceDataOutput, Types.Error>
    )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures GetExtendableResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)    
    {
      var rtnString: string := if input.stringValue.Some? then
        input.stringValue.value + " " + this.name
      else
        this.name;
      var rtn: Types.GetExtendableResourceDataOutput := Types.GetExtendableResourceDataOutput(
        blobValue := input.blobValue,
        booleanValue := input.booleanValue,
        stringValue := Some(rtnString),
        integerValue := input.integerValue,
        longValue := input.longValue
      );
      return Success(rtn);  
    }
    
    predicate AlwaysModeledErrorEnsuresPublicly(
      input: Types.GetExtendableResourceErrorsInput,
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    ) {true}

    method AlwaysModeledError'(
      input: Types.GetExtendableResourceErrorsInput
    ) returns (
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    )
      requires ValidState()
      modifies Modifies - {History}
      ensures ValidState()
      ensures AlwaysModeledErrorEnsuresPublicly(input, output)
      ensures unchanged(History)
      decreases Modifies - {History}
    {
      return Failure(Types.SimpleExtendableResourcesException(message := "Hard Coded Exception in src/dafny"));
    }
    
    predicate AlwaysOpaqueErrorEnsuresPublicly(
      input: Types.GetExtendableResourceErrorsInput,
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    ) {true}

    method AlwaysOpaqueError'(
      input: Types.GetExtendableResourceErrorsInput
    ) returns (
      output: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
    )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures AlwaysOpaqueErrorEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      var obj: object := new OpaqueMessage();
      return Failure(Types.Opaque(obj, "lost in translation"));
    }
  }
}
