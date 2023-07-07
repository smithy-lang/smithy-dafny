// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
include "KeyMaterial.dfy"

module {:options "-functionSyntax:4"} CreateStaticKeyStores {
  // import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import opened AwsCryptographyKeyStoreTypes
  import KeyMaterial

  method CreateStaticKeyStore( staticKeyMaterial : KeyMaterial.KeyMaterial )
    returns (keyStore: IKeyStoreClient)
    requires staticKeyMaterial.StaticKeyStoreInformation?
    ensures
      && keyStore.ValidState()
      && fresh(keyStore)
      && fresh(keyStore.Modifies)
  {
    return new StaticKeyStore(staticKeyMaterial);
  }

  // The goal of this class is to return *invalid* materials.
  // The CMM MUST check that the materials it gets are valid
  // So this keyring can be configured to return materials
  // that MUST fail this check.
  // This is *NOT* at example of a properly desgined keyring!
  class StaticKeyStore extends IKeyStoreClient
  {
    constructor(staticKeyMaterial : KeyMaterial.KeyMaterial)
      requires staticKeyMaterial.StaticKeyStoreInformation?
      ensures
        && ValidState()
        && fresh(History)
        && fresh(Modifies)
    {
      this.staticKeyMaterial := staticKeyMaterial;
      History := new IKeyStoreClientCallHistory();
      Modifies := {History};
    }

    const staticKeyMaterial : KeyMaterial.KeyMaterial

    ghost predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && staticKeyMaterial.StaticKeyStoreInformation?
    }

    // These are the supported Static information

    ghost predicate GetActiveBranchKeyEnsuresPublicly(input: GetActiveBranchKeyInput , output: Result<GetActiveBranchKeyOutput, Error>)
    {true}
    // The public method to be called by library consumers
    method GetActiveBranchKey ( input: GetActiveBranchKeyInput )
      returns (output: Result<GetActiveBranchKeyOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetActiveBranchKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetActiveBranchKeyEnsuresPublicly(input, output)
      ensures History.GetActiveBranchKey == old(History.GetActiveBranchKey) + [DafnyCallEvent(input, output)]
    {

      output := Success(GetActiveBranchKeyOutput(
                          branchKeyMaterials := BranchKeyMaterials(
                            branchKeyIdentifier := input.branchKeyIdentifier,
                            branchKeyVersion := staticKeyMaterial.branchKeyVersion,
                            branchKey := staticKeyMaterial.branchKey
                          )
                        ));

      History.GetActiveBranchKey := History.GetActiveBranchKey + [DafnyCallEvent(input, output)];
    }

    ghost predicate GetBranchKeyVersionEnsuresPublicly(input: GetBranchKeyVersionInput , output: Result<GetBranchKeyVersionOutput, Error>)
    {true}
    // The public method to be called by library consumers
    method GetBranchKeyVersion ( input: GetBranchKeyVersionInput )
      returns (output: Result<GetBranchKeyVersionOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetBranchKeyVersion
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetBranchKeyVersionEnsuresPublicly(input, output)
      ensures History.GetBranchKeyVersion == old(History.GetBranchKeyVersion) + [DafnyCallEvent(input, output)]
    {
      output := Success(GetBranchKeyVersionOutput(
                          branchKeyMaterials := BranchKeyMaterials(
                            branchKeyIdentifier := input.branchKeyIdentifier,
                            branchKeyVersion := staticKeyMaterial.branchKeyVersion,
                            branchKey := staticKeyMaterial.branchKey
                          )
                        ));
      History.GetBranchKeyVersion := History.GetBranchKeyVersion + [DafnyCallEvent(input, output)];
    }

    ghost predicate GetBeaconKeyEnsuresPublicly(input: GetBeaconKeyInput , output: Result<GetBeaconKeyOutput, Error>)
    {true}
    // The public method to be called by library consumers
    method GetBeaconKey ( input: GetBeaconKeyInput )
      returns (output: Result<GetBeaconKeyOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetBeaconKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetBeaconKeyEnsuresPublicly(input, output)
      ensures History.GetBeaconKey == old(History.GetBeaconKey) + [DafnyCallEvent(input, output)]
    {

      output := Success(GetBeaconKeyOutput(
                          beaconKeyMaterials := BeaconKeyMaterials(
                            beaconKeyIdentifier := input.branchKeyIdentifier,
                            beaconKey := Some(staticKeyMaterial.beaconKey),
                            hmacKeys := None
                          )));
      History.GetBeaconKey := History.GetBeaconKey + [DafnyCallEvent(input, output)];
    }

    // These are all not supported operations in a static context

    ghost predicate GetKeyStoreInfoEnsuresPublicly(output: Result<GetKeyStoreInfoOutput, Error>)
    {true}

    method GetKeyStoreInfo()
      returns (output: Result<GetKeyStoreInfoOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetKeyStoreInfo
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetKeyStoreInfoEnsuresPublicly(output)
      ensures History.GetKeyStoreInfo == old(History.GetKeyStoreInfo) + [DafnyCallEvent((), output)]
    {
      output := Failure(KeyStoreException( message := "Not Supported"));
      History.GetKeyStoreInfo := History.GetKeyStoreInfo + [DafnyCallEvent((), output)];
    }

    ghost predicate CreateKeyStoreEnsuresPublicly(input: CreateKeyStoreInput , output: Result<CreateKeyStoreOutput, Error>)
    {true}
    // The public method to be called by library consumers
    method CreateKeyStore ( input: CreateKeyStoreInput )
      returns (output: Result<CreateKeyStoreOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateKeyStoreEnsuresPublicly(input, output)
      ensures History.CreateKeyStore == old(History.CreateKeyStore) + [DafnyCallEvent(input, output)]
    {
      output := Failure(KeyStoreException( message := "Not Supported"));
      History.CreateKeyStore := History.CreateKeyStore + [DafnyCallEvent(input, output)];
    }

    ghost predicate CreateKeyEnsuresPublicly(input: CreateKeyInput, output: Result<CreateKeyOutput, Error>)
    {true}
    // The public method to be called by library consumers
    method CreateKey ( input: CreateKeyInput )
      returns (output: Result<CreateKeyOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateKeyEnsuresPublicly(input, output)
      ensures History.CreateKey == old(History.CreateKey) + [DafnyCallEvent(input, output)]
    {
      output := Failure(KeyStoreException( message := "Not Supported"));
      History.CreateKey := History.CreateKey + [DafnyCallEvent(input, output)];
    }

    ghost predicate VersionKeyEnsuresPublicly(input: VersionKeyInput , output: Result<(), Error>)
    {true}
    // The public method to be called by library consumers
    method VersionKey ( input: VersionKeyInput )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`VersionKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures VersionKeyEnsuresPublicly(input, output)
      ensures History.VersionKey == old(History.VersionKey) + [DafnyCallEvent(input, output)]
    {
      output := Failure(KeyStoreException( message := "Not Supported"));
      History.VersionKey := History.VersionKey + [DafnyCallEvent(input, output)];
    }

    ghost predicate BranchKeyStatusResolutionEnsuresPublicly(input: BranchKeyStatusResolutionInput , output: Result<(), Error>)
    {true}
    // The public method to be called by library consumers
    method BranchKeyStatusResolution ( input: BranchKeyStatusResolutionInput )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`BranchKeyStatusResolution
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures BranchKeyStatusResolutionEnsuresPublicly(input, output)
      ensures History.BranchKeyStatusResolution == old(History.BranchKeyStatusResolution) + [DafnyCallEvent(input, output)]
    {
      output := Failure(KeyStoreException( message := "Not Supported"));
      History.BranchKeyStatusResolution := History.BranchKeyStatusResolution + [DafnyCallEvent(input, output)];
    }

  }
}
