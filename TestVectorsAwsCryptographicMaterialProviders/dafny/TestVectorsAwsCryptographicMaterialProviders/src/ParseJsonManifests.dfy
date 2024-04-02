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
      var tail :- BuildEncryptTestVector(keys, obj[1..]);
      var encryptVector :- ToEncryptTestVector(keys, obj[0].0, obj[0].1);
      Success([ encryptVector ] + tail)
  }
  by method {
    // This function ideally would be`{:tailrecursion}`
    // at the time this did not seem simple.
    // Here is an example of how to make it tail recursive that may work.
    // However, we're leaving this as "by method"
    // to avoid changing anything and to provide an example of how to do that

    // function {:tailrecursion} BuildEncryptTestVector2(
    //   keys: KeyVectors.KeyVectorsClient,
    //   obj: seq<(string, JSON)>,
    //   acc : seq<EncryptTestVector> := []
    // )
    //   : Result<seq<EncryptTestVector>, string>
    // {
    //   if |obj| == 0 then
    //     Success(acc)
    //   else
    //     var encryptVector :- ToEncryptTestVector(keys, obj[0].0, obj[0].1);
    //     BuildEncryptTestVector2(keys, obj[1..], acc + [encryptVector])
    // }

    var i: nat := |obj|;
    var vectors := [];

    while i != 0
      decreases i
      invariant Success(vectors) == BuildEncryptTestVector(keys, obj[i..])
    {
      i := i - 1;
      var test := ToEncryptTestVector(keys, obj[i].0, obj[i].1);
      if test.Failure? {
        ghost var j := i;
        while j != 0
          decreases j
          invariant Failure(test.error) == BuildEncryptTestVector(keys, obj[j..])
        {
          j := j - 1;
        }
        return Failure(test.error);
      }

      vectors := [test.value] + vectors;
    }

    return Success(vectors);
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

    var algorithmSuite :- GetAlgorithmSuiteInfo(obj);
    var requiredEncryptionContextKeys :- GetRequiredEncryptionContextKeys(obj);
    var reproducedEncryptionContext :- GetReproducedEncryptionContext(obj);

    // TODO fix me
    var commitmentPolicy := CompleteVectors.AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite);
    // This MAY be too flexible. If the length is say a string, this will return None
    var maxPlaintextLength := GetPositiveLong("maxPlaintextLength", obj).ToOption();

    match typ
    case "positive-keyring" =>
      var encryptKeyDescription :- GetKeyDescription(keys, "encryptKeyDescription", obj);
      var decryptKeyDescription :- GetKeyDescription(keys, "decryptKeyDescription", obj);

      Success(PositiveEncryptKeyringVector(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                maxPlaintextLength := maxPlaintextLength,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                encryptDescription := encryptKeyDescription,
                decryptDescription := decryptKeyDescription,
                reproducedEncryptionContext := reproducedEncryptionContext
              ))
    case "negative-encrypt-keyring" =>
      var keyDescription :- GetKeyDescription(keys, "keyDescription", obj);
      var errorDescription :- GetString("errorDescription", obj);
      :- Need(reproducedEncryptionContext.None?, "reproducedEncryptionContext not supported");

      Success(NegativeEncryptKeyringVector(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                maxPlaintextLength := maxPlaintextLength,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                errorDescription := errorDescription,
                keyDescription := keyDescription
              ))

    case "negative-decrypt-keyring" =>
      var encryptKeyDescription :- GetKeyDescription(keys, "encryptKeyDescription", obj);
      var decryptKeyDescription :- GetKeyDescription(keys, "decryptKeyDescription", obj);
      var decryptErrorDescription :- GetString("decryptErrorDescription", obj);

      Success(PositiveEncryptNegativeDecryptKeyringVector(
                name := name,
                description := description,
                decryptErrorDescription := decryptErrorDescription,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                maxPlaintextLength := maxPlaintextLength,
                requiredEncryptionContextKeys := requiredEncryptionContextKeys,
                encryptDescription := encryptKeyDescription,
                decryptDescription := decryptKeyDescription,
                reproducedEncryptionContext := reproducedEncryptionContext
              ))

    case _ => Failure("Unsupported EncryptTestVector type:" + typ)
  }

  function GetKeyDescription(
    keyVectorClient: KeyVectors.KeyVectorsClient,
    key: string,
    obj: seq<(string, JSON)>
  )
    : Result<KeyVectorsTypes.KeyDescription, string>
  {
    var keyDescriptionObject :- Get(key, obj);

    // Be nice if `document` mapped to `JSON.Values.JSON`
    var descriptionStr :- API.Serialize(keyDescriptionObject)
                          .MapFailure((e: Errors.SerializationError) => e.ToString());

    var keyDescriptionOutput :- keyVectorClient
                                .GetKeyDescription(KeyVectorsTypes.GetKeyDescriptionInput(
                                                     json := descriptionStr
                                                   ))
                                .MapFailure(ErrorToString);

    Success(keyDescriptionOutput.keyDescription)
  }

  function GetAlgorithmSuiteInfo(
    obj: seq<(string, JSON)>
  ) : Result<Types.AlgorithmSuiteInfo, string>
  {
    var algorithmSuiteHex :- GetString("algorithmSuiteId", obj);
    :- Need(HexStrings.IsLooseHexString(algorithmSuiteHex), "Not hex encoded binary");
    var binaryId := HexStrings.FromHexString(algorithmSuiteHex);
    // TODO change this to use AlgorithmSuiteInfoByHexString
    AlgorithmSuites
    .GetAlgorithmSuiteInfo(binaryId)
    .MapFailure(e => "Invalid Suite:" + algorithmSuiteHex)
  }

  function GetRequiredEncryptionContextKeys(
    obj: seq<(string, JSON)>
  ) : Result<Option<seq<UTF8.ValidUTF8Bytes>>, string>
  {
    var keysAsStrings := GetArrayString("requiredEncryptionContextKeys", obj).ToOption();
    match keysAsStrings
    case Some(s) =>
      var k :- utf8EncodeSeq(keysAsStrings.value);
      Success(Some(k))
    case None() => Success(None())
  }

  function GetReproducedEncryptionContext(
    obj: seq<(string, JSON)>
  ) : Result<Option<map<UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes>>, string>
  {
    var reproducedEncryptionContextStrings :- GetOptionalSmallObjectToStringStringMap("reproducedEncryptionContext", obj);
    match reproducedEncryptionContextStrings
    case Some(r) =>
      var e :- utf8EncodeMap(r);
      Success(Some(e))
    case None() => Success(None())
  }

  function ErrorToString(e: KeyVectorsTypes.Error): string
  {
    match e
    case KeyVectorException(message) => message
    case AwsCryptographyMaterialProviders(mplError) => (
      match mplError
      case AwsCryptographicMaterialProvidersException(message) => message
      case _ => "Unmapped AwsCryptographyMaterialProviders" )
    case _ => "Unmapped KeyVectorException"
  }

  function BuildDecryptTestVector(keys: KeyVectors.KeyVectorsClient, obj: seq<(string, JSON)>)
    : Result<seq<DecryptTestVector>, string>
  {
    if |obj| == 0 then
      Success([])
    else
      var tail :- BuildDecryptTestVector(keys, obj[1..]);
      var encryptVector :- ToDecryptTestVector(keys, obj[0].0, obj[0].1);
      Success([ encryptVector ] + tail)
  }
  by method {
    // This function ideally would be`{:tailrecursion}`
    // but it is not simple to here is a method
    // so that it does not explode with huge numbers of tests.
    var i: nat := |obj|;
    var vectors := [];

    while i != 0
      decreases i
      invariant Success(vectors) == BuildDecryptTestVector(keys, obj[i..])
    {
      i := i - 1;
      var test := ToDecryptTestVector(keys, obj[i].0, obj[i].1);
      if test.Failure? {
        ghost var j := i;
        while j != 0
          decreases j
          invariant Failure(test.error) == BuildDecryptTestVector(keys, obj[j..])
        {
          j := j - 1;
        }
        return Failure(test.error);
      }

      vectors := [test.value] + vectors;
    }

    return Success(vectors);
  }


  function printJson(j: seq<(string, JSON)>) : (){()} by method {print j, "\n", "\n"; return ();}

  function GetEncryptedDataKeys(obj: seq<(string, JSON)>)
    : Result<Types.EncryptedDataKeyList, string>
  {
    var encryptedDataKeysJson :- GetArray("encryptedDataKeys", obj);
    Seq.MapWithResult(GetEncryptedDataKey, encryptedDataKeysJson)
  }

  function GetEncryptedDataKey(json: JSON)
    : Result<Types.EncryptedDataKey, string>
  {
    :- Need(json.Object?, "Encrypted data key is not an object");
    var keyProviderId :- GetString("keyProviderId", json.obj);
    var keyProviderInfo :- GetString("keyProviderInfo", json.obj);
    var ciphertext :- GetString("ciphertext", json.obj);

    var keyProviderId :- UTF8.Encode(keyProviderId);
    var keyProviderInfo :- Base64.Decode(keyProviderInfo);
    var ciphertext :- Base64.Decode(ciphertext);

    Success(Types.EncryptedDataKey(
              keyProviderId := keyProviderId,
              keyProviderInfo := keyProviderInfo,
              ciphertext := ciphertext
            ))
  }

  function GetExpectedResult(obj: seq<(string, JSON)>)
    : Result<DecryptResult, string>
  {
    var result :- GetObject("result", obj);
    var plaintextDataKey :- GetOptionalString("plaintextDataKey", result);
    var symmetricSigningKey :- GetOptionalString("symmetricSigningKey", result);
    var requiredEncryptionContextKeys :- GetArrayString("requiredEncryptionContextKeys", result);

    var plaintextDataKey :- if plaintextDataKey.Some? then
                              var p :- Base64.Decode(plaintextDataKey.value);
                              Success(Some(p))
                            else Success(None);
    var symmetricSigningKey :- if symmetricSigningKey.Some? then
                                 var p :- Base64.Decode(symmetricSigningKey.value);
                                 Success(Some(p))
                               else Success(None);
    var requiredEncryptionContextKeys :- utf8EncodeSeq(requiredEncryptionContextKeys);

    Success(DecryptResult(
              plaintextDataKey := plaintextDataKey,
              symmetricSigningKey := symmetricSigningKey,
              requiredEncryptionContextKeys := requiredEncryptionContextKeys
            ))
  }

  function ToDecryptTestVector(keys: KeyVectors.KeyVectorsClient, name: string, json: JSON)
    : Result<DecryptTestVector, string>
  {
    :- Need(json.Object?, "DecryptTestVector not an object");
    var obj := json.obj;
    var typString := "type";
    var typ :- GetString(typString, obj);

    var description :- GetOptionalString("description", obj);

    var encryptionContextStrings :- SmallObjectToStringStringMap("encryptionContext", obj);
    var encryptionContext :- utf8EncodeMap(encryptionContextStrings);

    var algorithmSuite :- GetAlgorithmSuiteInfo(obj);
    var reproducedEncryptionContext :- GetReproducedEncryptionContext(obj);

    // TODO fix me
    var commitmentPolicy := CompleteVectors.AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite);
    var keyDescription :- GetKeyDescription(keys, "keyDescription", obj);
    var encryptedDataKeys :- GetEncryptedDataKeys(obj);

    match typ
    case "positive-keyring" =>
      var expectedResult :- GetExpectedResult(obj);
      Success(PositiveDecryptKeyringTest(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                keyDescription := keyDescription,
                encryptedDataKeys := encryptedDataKeys,
                expectedResult := expectedResult,
                reproducedEncryptionContext := reproducedEncryptionContext
              ))
    case "negative-keyring" =>
      var errorDescription :- GetString("errorDescription", obj);
      Success(NegativeDecryptKeyringTest(
                name := name,
                description := description,
                encryptionContext := encryptionContext,
                commitmentPolicy := commitmentPolicy,
                algorithmSuite := algorithmSuite,
                errorDescription := errorDescription,
                encryptedDataKeys := encryptedDataKeys,
                keyDescription := keyDescription,
                reproducedEncryptionContext := reproducedEncryptionContext
              ))

    case _ => Failure("Unsupported DecryptTestVector type:" + typ)
  }
}
