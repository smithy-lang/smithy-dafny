// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleOrphanedTypes.dfy"

// This resource is orphaned in the Smithy model.
module OrphanedResource {
  import opened StandardLibrary
  import opened Wrappers
  import Types = SimpleOrphanedTypes

  class OrphanedResource extends Types.IOrphanedResource
  {
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    constructor (
    )
    {
      History := new Types.IOrphanedResourceCallHistory();
      Modifies := {History};
    }

    predicate OrphanedResourceOperationEnsuresPublicly(
      input: Types.OrphanedResourceOperationInput,
      output: Result<Types.OrphanedResourceOperationOutput, Types.Error>
    ) {true}

    method OrphanedResourceOperation'(
      input: Types.OrphanedResourceOperationInput
    ) returns (
        output: Result<Types.OrphanedResourceOperationOutput, Types.Error>
      )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures && ValidState()
      ensures OrphanedResourceOperationEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      if (
          && input.someString.Some?
          && input.someString.value == "the extern MUST provide this string to the native resource's operation"
        ) {
        return Success(Types.OrphanedResourceOperationOutput(someString := Some("correct string")));
      } else {
        return Failure(Types.Error.OrphanedError(message := "incorrect string"));
      }
    }
  }
}
