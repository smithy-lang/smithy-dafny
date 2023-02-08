// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypes.dfy"

module ExtendableResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimpleExtendableResourcesTypes

  class OpaqueMessage {
    const message: string := "Hard Coded Opaque Message that will not survive translation.";
    constructor () {}
  }

  class ExtendableResource extends Types.IExtendableResource
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    constructor ()
      ensures ValidState() && fresh(History) && fresh(Modifies)
    {
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
      return Failure(Types.Collection([nestedError]));
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
      ensures ValidState()
      ensures GetResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)    
    {
      var rtn: Types.GetResourceDataOutput := Types.GetResourceDataOutput(
        blobValue := input.blobValue,
        booleanValue := input.booleanValue,
        stringValue := input.stringValue,
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
      return Failure(Types.Opaque(obj));
    }
  }
}
