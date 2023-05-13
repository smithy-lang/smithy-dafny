// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypesWrapped.dfy"
include "JSONHelpers.dfy"
include "TestVectors.dfy"
include "CompleteVectors.dfy"

module {:options "-functionSyntax:4"} ParseJsonManifests {

  import Types = AwsCryptographyMaterialProvidersTypes

  import JSON.API
  import opened JSON.Values
  import JSON.Errors
  import opened Wrappers
  import UTF8
  import Seq
  import opened StandardLibrary.UInt
  import BoundedInts
  import opened JSONHelpers
  import opened TestVectors
  import HexStrings
  import Base64
  import CompleteVectors
  import KeyVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
    // This is a HACK!
    // This is *ONLY* because this is wrapping the MPL
  import AlgorithmSuites

  function BuildEncryptTestVector(keys: KeyVectors.KeyVectorsClient, obj: seq<(string, JSON)>)
    : Result<seq<EncryptTestVector>, string>
  {
    if |obj| == 0 then
      Success([])
    else
      var name := obj[0].0;
      var encryptVector :- ToEncryptTestVector(keys, name, obj[0].1);
      var tail :- BuildEncryptTestVector(keys, obj[1..]);
      Success([ encryptVector ] + tail)
  }

  function ToEncryptTestVector(keys: KeyVectors.KeyVectorsClient, name: string, obj: JSON)
    : Result<EncryptTestVector, string>
  {
    :- Need(obj.Object?, "EncryptTestVector not an object");
    var obj := obj.obj;
    var typString := "type";
    var typ :- GetString(typString, obj);

    var description := GetString("description", obj).ToOption();

    var encryptionContextStrings :- SmallObjectToStringStringMap("encryptionContext", obj);
    var encryptionContext :- utf8EncodeMap(encryptionContextStrings);

    // TODO change this to use AlgorithmSuiteInfoByHexString
    var algorithmSuiteHex :- GetString("algorithmSuiteId", obj);
    :- Need(HexStrings.IsLooseHexString(algorithmSuiteHex), "Not hex encoded binnary");
    var binaryId := HexStrings.FromHexString(algorithmSuiteHex);
    var algorithmSuite :- AlgorithmSuites
                          .GetAlgorithmSuiteInfo(binaryId)
                          .MapFailure(e => "Invalid Suite:" + algorithmSuiteHex);

    var keysAsStrings := GetArrayString("requiredEncryptionContextKeys", obj).ToOption();
    var requiredEncryptionContextKeys :- if keysAsStrings.Some? then
                                           var result := utf8EncodeSeq(keysAsStrings.value);
                                           if result.Success? then Success(Some(result.value)) else Failure(result.error)
                                         else Success(None);

    // TODO fix me
    var commitmentPolicy := CompleteVectors.GetCompatableCommitmentPolicy(algorithmSuite);
    var maxPlaintextLength := None; // GetString("maxPlaintextLength", obj);

    match typ
    case "positive-keyring" =>
      var encryptKeyDescriptionObject :- Get("encryptKeyDescription", obj);
      var decryptKeyDescriptionObject :- Get("decryptKeyDescription", obj);

      // Be nice if `document` mapped to `JSON.Values.JSON`
      var encryptStr :- API.Serialize(encryptKeyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString());
      var decryptStr :- API.Serialize(decryptKeyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString());

      var encryptKeyDescription :- keys
                                   .GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(
                                                        json := encryptStr
                                                      ))
                                   .MapFailure(ErrorToString);

      var decryptKeyDescription :- keys
                                   .GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(
                                                        json := decryptStr
                                                      ))
                                   .MapFailure(ErrorToString);
      Success(PositiveEncryptKeyringVector(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                maxPlaintextLength := maxPlaintextLength,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                encryptDescription := encryptKeyDescription.keyDescription,
                decryptDescription := decryptKeyDescription.keyDescription
              ))
    case "negative-keyring" =>
      var keyDescriptionObject :- Get("keyDescription", obj);
      var keyStr :- API.Serialize(keyDescriptionObject).MapFailure((e: Errors.SerializationError) => e.ToString());
      var keyDescription :- keys
                            .GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(
                                                 json := keyStr
                                               ))
                            .MapFailure(ErrorToString);

      var errorDescription :- GetString("errorDescription", obj);
      Success(NegativeEncryptKeyringVector(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                maxPlaintextLength := maxPlaintextLength,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                errorDescription := errorDescription,
                keyDescription := keyDescription.keyDescription
              ))
    case _ => Failure("Unsupported EncryptTestVector type:" + typ)
  }

  function ErrorToString(e: KeyVectorsTypes.Error): string
  {
    match e
    case KeyVectorException(message) => message
    case AwsCryptographyMaterialProviders(mplError) => ( match mplError
                                                         case AwsCryptographicMaterialProvidersException(message) => message
                                                         case _ => "Umapped AwsCryptographyMaterialProviders" )
    case _ => "Umapped KeyVectorException"
  }
}
