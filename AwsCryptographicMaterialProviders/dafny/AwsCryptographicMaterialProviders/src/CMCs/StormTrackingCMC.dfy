// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "StormTracker.dfy"

module {:options "/functionSyntax:4" } {:extern "software.amazon.cryptography.internaldafny.StormTrackingCMC" } StormTrackingCMC {
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes
  import StormTracker

  class {:extern} StormTrackingCMC extends Types.ICryptographicMaterialsCache {

    ghost predicate ValidState()
      reads this`Modifies, Modifies - {History}
      ensures ValidState() ==> History in Modifies
    {
      History in Modifies
    }

    constructor {:extern} (
      wrapped: StormTracker.StormTracker
    )
      ensures
        && ValidState()
        && fresh(this.Modifies)


    ghost predicate GetCacheEntryEnsuresPublicly(input: Types.GetCacheEntryInput, output: Result<Types.GetCacheEntryOutput, Types.Error>)
    {true}

    method {:extern "GetCacheEntry"}  GetCacheEntry'(input: Types.GetCacheEntryInput)
      returns (output: Result<Types.GetCacheEntryOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures GetCacheEntryEnsuresPublicly(input, output)
      ensures unchanged(History)

    ghost predicate PutCacheEntryEnsuresPublicly(input: Types.PutCacheEntryInput, output: Result<(), Types.Error>)
    {true}

    method {:extern "PutCacheEntry"} PutCacheEntry' (input: Types.PutCacheEntryInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures PutCacheEntryEnsuresPublicly(input, output)
      ensures unchanged(History)

    ghost predicate DeleteCacheEntryEnsuresPublicly(input: Types.DeleteCacheEntryInput, output: Result<(), Types.Error>)
    {true}

    method {:extern "DeleteCacheEntry"} DeleteCacheEntry'(input: Types.DeleteCacheEntryInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures DeleteCacheEntryEnsuresPublicly(input, output)
      ensures unchanged(History)
      ensures Modifies <= old(Modifies)

    ghost predicate UpdateUsageMetadataEnsuresPublicly(input: Types.UpdateUsageMetadataInput, output: Result<(), Types.Error>)
    {true}

    method {:extern "UpdateUsageMetadata"} UpdateUsageMetadata'(input: Types.UpdateUsageMetadataInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()

  }
}
