// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
  // Yes, this is reaching across.
  // idealy all these functions would exist in the STD Library.
include "../../TestVectorsAwsCryptographicMaterialProviders/src/JSONHelpers.dfy"

module {:options "-functionSyntax:4"} KeyMaterial {

  import MPL = AwsCryptographyMaterialProvidersTypes

  import opened JSON.Values
  import opened Wrappers
  import Seq
  import opened StandardLibrary.UInt
  import opened JSONHelpers
  import HexStrings
  import Base64

  function BuildKeyMaterials(
    mpl: MPL.IAwsCryptographicMaterialProvidersClient,
    obj: seq<(string, JSON)>)
    : Result<map<string, KeyMaterial>, string>
  {
    if |obj| == 0 then
      Success(map[])
    else
      var name := obj[0].0;
      var keyMaterial :- ToKeyMaterial(mpl, name, obj[0].1);
      var tail :- BuildKeyMaterials(mpl, obj[1..]);
      Success(map[ name := keyMaterial] + tail)
  }

  function ToKeyMaterial(
    mpl: MPL.IAwsCryptographicMaterialProvidersClient,
    name: string, obj: JSON
  ): Result<KeyMaterial, string>
  {
    :- Need(obj.Object?, "KeyDescription not an object");
    var obj := obj.obj;
    var typString := "type";
    var typ :- GetString(typString, obj);

    :- Need(KeyMaterialString?(typ), "Unsupported KeyMaterial type:" + typ);

    match typ
    case "static-material" =>
      var algorithmSuiteHex :- GetString("algorithmSuiteId", obj);
      :- Need(HexStrings.IsLooseHexString(algorithmSuiteHex), "Not hex encoded binnary");
      var binaryId := HexStrings.FromHexString(algorithmSuiteHex);
      var algorithmSuite :- mpl.GetAlgorithmSuiteInfo(binaryId)
                            .MapFailure(e => "Invalid Suite:" + algorithmSuiteHex);

      var encryptionContextStrings :- SmallObjectToStringStringMap("encryptionContext", obj);
      var encryptionContext :- utf8EncodeMap(encryptionContextStrings);

      var keysAsStrings :- GetArrayString("requiredEncryptionContextKeys", obj);
      var requiredEncryptionContextKeys :- utf8EncodeSeq(keysAsStrings);

      var encryptedDataKeysJSON :- GetArrayObject("encryptedDataKeys", obj);
      var encryptedDataKeys :- Seq.MapWithResult(ToEncryptedDataKey, encryptedDataKeysJSON);

      var plaintextDataKeyEncoded :- GetOptionalString("plaintextDataKey", obj);
      var plaintextDataKey :- if plaintextDataKeyEncoded.Some? then
                                var result := Base64.Decode(plaintextDataKeyEncoded.value);
                                if result.Success? then Success(Some(result.value)) else Failure(result.error)
                              else Success(None);
      var signingKey :- GetOptionalString("signingKey", obj);
      var verificationKey :- GetOptionalString("verificationKey", obj);
      var symmetricSigningKeys := GetArrayString("symmetricSigningKeys", obj).ToOption();

      Success(StaticMaterial(
                name := name,
                algorithmSuite := algorithmSuite,
                encryptionContext := encryptionContext,
                encryptedDataKeys := encryptedDataKeys,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                plaintextDataKey := plaintextDataKey,
                // This is just for now...
                signingKey := None,
                verificationKey := None,
                symmetricSigningKeys := None
              ))
    case "static-branch-key" =>
      var keyIdentifier :- GetString("key-id", obj);

      var branchKeyVersionEncoded :- GetString("branchKeyVersion", obj);
      var branchKeyVersion :- UTF8.Encode(branchKeyVersionEncoded);
      var branchKeyEncoded :- GetString("branchKey", obj);
      var branchKey :- Base64.Decode(branchKeyEncoded);
      var beaconKeyEncoded :- GetString("beaconKey", obj);
      var beaconKey :- Base64.Decode(beaconKeyEncoded);

      Success(StaticKeyStoreInformation(
                keyIdentifier := keyIdentifier,
                branchKeyVersion := branchKeyVersion,
                branchKey := branchKey,
                beaconKey := beaconKey
              ))
    case _ =>
      var encrypt :- GetBool("encrypt", obj);
      var decrypt :- GetBool("decrypt", obj);
      var keyIdentifier :- GetString("key-id", obj);

      match typ
      case "aws-kms" =>
        Success(KeyMaterial.KMS(
                  name := name,
                  encrypt := encrypt,
                  decrypt := decrypt,
                  keyIdentifier := keyIdentifier
                ))
      case _ =>
        var algorithm :- GetString("algorithm", obj);
        var bits :- GetNat("bits", obj);
        var encoding :- GetString("encoding", obj);
        var material :- GetString("material", obj);

        match typ
        case "symmetric" =>
          var materialBytes :- Base64.Decode(material);
          Success(Symetric(
                    name := name,
                    encrypt := encrypt,
                    decrypt := decrypt,
                    keyIdentifier := keyIdentifier,
                    algorithm := algorithm,
                    bits := bits,
                    encoding := encoding,
                    wrappingKey := materialBytes
                  ))
        case "private" =>
          Success(PrivateRSA(
                    name := name,
                    encrypt := encrypt,
                    decrypt := decrypt,
                    keyIdentifier := keyIdentifier,
                    algorithm := algorithm,
                    bits := bits,
                    encoding := encoding,
                    material := material
                  ))
        case "public" =>
          Success(PublicRSA(
                    name := name,
                    encrypt := encrypt,
                    decrypt := decrypt,
                    keyIdentifier := keyIdentifier,
                    algorithm := algorithm,
                    bits := bits,
                    encoding := encoding,
                    material := material
                  ))
        case "aws-kms-rsa" =>
        var publicKey :- UTF8.Encode(material);

          Success(KMSAsymetric(
                    name := name,
                    encrypt := encrypt,
                    decrypt := decrypt,
                    keyIdentifier := keyIdentifier,
                    algorithm := algorithm,
                    bits := bits,
                    encoding := encoding,
                    publicKey := publicKey
                  ))
  }

  function ToEncryptedDataKey(obj: seq<(string, JSON)>)
    : Result<MPL.EncryptedDataKey, string>
  {
    var keyProviderIdJSON :- GetString("keyProviderId", obj);
    var keyProviderInfoJSON :- GetString("keyProviderInfo", obj);
    var ciphertextJSON :- GetString("ciphertext", obj);

    var keyProviderId :- UTF8.Encode(keyProviderIdJSON);
    var keyProviderInfo :- Base64.Decode(keyProviderInfoJSON);
    var ciphertext :- Base64.Decode(ciphertextJSON);

    Success(MPL.EncryptedDataKey(
              keyProviderId := keyProviderId,
              keyProviderInfo := keyProviderInfo,
              ciphertext := ciphertext
            ))
  }

  predicate KeyMaterialString?(s: string)
  {
    || s == "static-material"
    || s == "aws-kms"
    || s == "symmetric"
    || s == "private"
    || s == "public"
    || s == "static-branch-key"
    || s == "aws-kms-rsa"
  }

  datatype KeyMaterial =
    | Symetric(
        name: string,
        encrypt: bool, decrypt: bool,
        algorithm: string,
        bits: nat,
        encoding: string,
        wrappingKey: MPL.Secret,
        keyIdentifier: string
      )
    | PrivateRSA(
        name: string,
        encrypt: bool, decrypt: bool,
        algorithm: string,
        bits: nat,
        encoding: string,
        material: string,
        keyIdentifier: string
      )
    | PublicRSA(
        name: string,
        encrypt: bool, decrypt: bool,
        bits: nat,
        algorithm: string,
        encoding: string,
        material: string,
        keyIdentifier: string
      )
    | KMS(
        name: string,
        encrypt: bool, decrypt: bool,
        keyIdentifier: string
      )
    | KMSAsymetric(
        name: string,
        encrypt: bool, decrypt: bool,
        keyIdentifier: string,
        bits: nat,
        algorithm: string,
        encoding: string,
        publicKey: MPL.Secret
      )
    | StaticMaterial(
        name: string,
        algorithmSuite: MPL.AlgorithmSuiteInfo,
        encryptionContext: MPL.EncryptionContext,
        encryptedDataKeys: MPL.EncryptedDataKeyList,
        requiredEncryptionContextKeys: MPL.EncryptionContextKeys,
        plaintextDataKey: Option<MPL.Secret> := None,
        signingKey: Option<MPL.Secret> := None,
        verificationKey: Option<MPL.Secret> := None,
        symmetricSigningKeys: Option<MPL.SymmetricSigningKeyList> := None
      )
    | StaticKeyStoreInformation(
        keyIdentifier: string,
        branchKeyVersion: MPL.Utf8Bytes,
        branchKey: MPL.Secret,
        beaconKey: MPL.Secret
      )

}
