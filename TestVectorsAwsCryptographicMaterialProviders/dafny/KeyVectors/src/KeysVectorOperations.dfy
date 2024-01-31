// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
  // Yes, this is reaching across.
  // ideally all these functions would exist in the STD Library.
include "../../TestVectorsAwsCryptographicMaterialProviders/src/LibraryIndex.dfy"
include "../../TestVectorsAwsCryptographicMaterialProviders/src/JSONHelpers.dfy"
include "KeyDescription.dfy"
include "KeyMaterial.dfy"
include "KeyringFromKeyDescription.dfy"
include "CmmFromKeyDescription.dfy"

module {:options "-functionSyntax:4"} KeysVectorOperations refines AbstractAwsCryptographyMaterialProvidersTestVectorKeysOperations {
  import JSON.API
  import JSON.Errors
  import JSON.Values
  import KeyDescription
  import MPL = AwsCryptographyMaterialProvidersTypes
  import KeyMaterial
  import KeyringFromKeyDescription
  import CmmFromKeyDescription
  import WrappedMaterialProviders
  import MaterialProviders

  datatype Config = Config(
    keys: map<string, KeyMaterial.KeyMaterial>,
    keysJson: Values.JSON
  )

  type InternalConfig = Config
  ghost predicate ValidInternalConfig?(config: InternalConfig)
  {
    true
  }
  ghost function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {
    {}
  }

  predicate CreateTestVectorKeyringEnsuresPublicly(
    input: TestVectorKeyringInput ,
    output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
  {true}
  method CreateTestVectorKeyring ( config: InternalConfig , input: TestVectorKeyringInput )
    returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
  {

    :- Need(KeyDescription.Keyring?(input.keyDescription),
            KeyVectorException( message := "Only Keyring key descriptions are supported.")
    );

    var maybeMpl := MaterialProviders.MaterialProviders();
    var mpl :- maybeMpl.MapFailure(e => AwsCryptographyMaterialProviders(e));

    output := KeyringFromKeyDescription.ToKeyring(mpl, config.keys, input.keyDescription);
  }

  predicate CreateWrappedTestVectorKeyringEnsuresPublicly(input: TestVectorKeyringInput ,
                                                          output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
  {true}

  method CreateWrappedTestVectorKeyring ( config: InternalConfig , input: TestVectorKeyringInput )
    returns (output: Result<AwsCryptographyMaterialProvidersTypes.IKeyring, Error>)
  {

    :- Need(KeyDescription.Keyring?(input.keyDescription),
            KeyVectorException( message := "Only Keyring key descriptions are supported.")
    );

    var maybeMpl := WrappedMaterialProviders.WrappedMaterialProviders();
    var wrappedMPL :- maybeMpl.MapFailure(e => AwsCryptographyMaterialProviders(e));

    output := KeyringFromKeyDescription.ToKeyring(wrappedMPL, config.keys, input.keyDescription);
  }

  predicate CreateWrappedTestVectorCmmEnsuresPublicly(
    input: TestVectorCmmInput ,
    output: Result<AwsCryptographyMaterialProvidersTypes.ICryptographicMaterialsManager, Error>)
  {true}

  method CreateWrappedTestVectorCmm ( config: InternalConfig , input: TestVectorCmmInput )
    returns (output: Result<AwsCryptographyMaterialProvidersTypes.ICryptographicMaterialsManager, Error>)
  {
    var maybeMpl := WrappedMaterialProviders.WrappedMaterialProviders();
    var wrappedMPL :- maybeMpl.MapFailure(e => AwsCryptographyMaterialProviders(e));

    output := CmmFromKeyDescription.ToCmm(wrappedMPL, config.keys, input.keyDescription, input.forOperation);
  }

  function GetKeyDescription ( config: InternalConfig , input: GetKeyDescriptionInput )
    : (output: Result<GetKeyDescriptionOutput, Error>)
  {
    var keyDescriptionJSON :- API.Deserialize(input.json)
                              .MapFailure((e: Errors.DeserializationError)  => AwsCryptographyMaterialProviders(
                                              AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(
                                                message := e.ToString()
                                              )));
    var keyDescription :- KeyDescription.ToKeyDescription(keyDescriptionJSON)
                          .MapFailure(e => AwsCryptographyMaterialProviders(
                                          AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(
                                            message := e
                                          )));
    Success(GetKeyDescriptionOutput(
              keyDescription := keyDescription
            ))
  }

  function SerializeKeyDescription ( config: InternalConfig , input: SerializeKeyDescriptionInput )
    : (output: Result<SerializeKeyDescriptionOutput, Error>)
  {
    var json :- KeyDescription.ToJson(input.keyDescription, 2)
                .MapFailure((s)  => AwsCryptographyMaterialProviders(
                                AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(
                                  message := s
                                )));

    var jsonBytes :- API.Serialize(json)
                     .MapFailure((e: Errors.SerializationError)  => AwsCryptographyMaterialProviders(
                                     AwsCryptographyMaterialProvidersTypes.AwsCryptographicMaterialProvidersException(
                                       message := e.ToString()
                                     )));
    Success(SerializeKeyDescriptionOutput( json := jsonBytes ))
  }
}
