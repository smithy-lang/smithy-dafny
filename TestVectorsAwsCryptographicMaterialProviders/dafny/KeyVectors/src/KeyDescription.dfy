// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
  // Yes, this is reaching across.
  // ideally all these functions would exist in the STD Library.
include "../../TestVectorsAwsCryptographicMaterialProviders/src/JSONHelpers.dfy"

module {:options "-functionSyntax:4"} KeyDescription {
  import opened Wrappers
  import opened JSON.Values
  import AwsCryptographyMaterialProvidersTypes
  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import opened JSONHelpers
  import ComAmazonawsKmsTypes
  import Seq
  import Base64
  import UTF8

  function printErr(e: string) : (){()} by method {print e, "\n", "\n"; return ();}
  function printJSON(e: seq<(string, JSON)>) : (){()} by method {print e, "\n", "\n"; return ();}

  function ToKeyDescription(json: JSON)
    : Result<KeyDescription, string>
    decreases Size(json), 1
  {
    if json.Array? then
      :- Need(1 <= |json.arr|, "Need at least one element in a JSON Array.");
      :- Need(forall c <- json.arr :: c.Object?, "No nested arrays.");
      ElementsOfArrayWillDecreaseSize(json);
      ToMultiKeyring(json, Some(json.arr[0]), json.arr[1..])
    else
      :- Need(json.Object?, "KeyDescription not an object");
      var obj := json.obj;
      var typString := "type";
      var typ :- GetString(typString, obj);

      :- Need(KeyDescriptionString?(typ), "Unsupported KeyDescription type:" + typ);

      match typ
      case "aws-kms-mrk-aware-discovery" => ToAwsKmsMrkAwareDiscovery(obj)
      case "multi-keyring" =>
        var generatorJson := Get("generator", obj).ToOption();
        var childKeyringsJson :- GetArray("childKeyrings", obj);

        assert generatorJson.Some? ==> Size(generatorJson.value) < Size(json) by {
          if generatorJson.Some? {
            GetWillDecreaseSize("generator", generatorJson.value, json);
          }
        }
        GetWillDecreaseSize("childKeyrings", Array(childKeyringsJson), json);
        ElementsOfArrayWillDecreaseSize(Array(childKeyringsJson));

        ToMultiKeyring(json, generatorJson, childKeyringsJson)
      case "required-encryption-context-cmm" =>
        var u :- Get("underlying", obj);
        GetWillDecreaseSize("underlying", u, json);
        var underlying :- ToKeyDescription(u);
        var requiredEncryptionContextStrings
          := GetArrayString("requiredEncryptionContextKeys", obj)
             .ToOption()
             .UnwrapOr([]);
        var requiredEncryptionContextKeys :- utf8EncodeSeq(requiredEncryptionContextStrings);

        Success(RequiredEncryptionContext(
                  RequiredEncryptionContextCMM(
                    underlying := underlying,
                    requiredEncryptionContextKeys := requiredEncryptionContextKeys
                  )))
      case _ =>
        var key :- GetString("key", obj);
        match typ
        case "static-material-keyring" =>
          Success(Static(StaticKeyring( keyId := key )))
        case "aws-kms" =>
          Success(Kms(KMSInfo( keyId := key )))
        case "aws-kms-mrk-aware" =>
          Success(KmsMrk(KmsMrkAware( keyId := key )))
        case "aws-kms-rsa" => ToAwsKmsRsa(key, obj)
        case "aws-kms-hierarchy" =>
          Success(Hierarchy(HierarchyKeyring( keyId := key )))
        case "raw" =>
          var algorithm :- GetString("encryption-algorithm", obj);
          :- Need(RawAlgorithmString?(algorithm), "Unsupported algorithm:" + algorithm);
          match algorithm
          case "aes" => ToRawAes(key, obj)
          case "rsa" => ToRawRsa(key, obj)
  }

  function ToDiscoveryFilter(obj: seq<(string, JSON)>)
    : Option<AwsCryptographyMaterialProvidersTypes.DiscoveryFilter>
  {
    var filter :- GetObject("aws-kms-discovery-filter", obj).ToOption();
    var partition :- GetString("partition", filter).ToOption();
    var accountIds :- GetArrayString("account-ids", filter).ToOption();
    Some(AwsCryptographyMaterialProvidersTypes.DiscoveryFilter(
           partition := partition,
           accountIds := accountIds
         ))
  }

  function ToAwsKmsMrkAwareDiscovery(obj: seq<(string, JSON)>)
    : Result<KeyDescription, string>
  {
    var defaultMrkRegion :- GetString("default-mrk-region", obj);
    var filter := GetObject("aws-kms-discovery-filter", obj);
    var awsKmsDiscoveryFilter := ToDiscoveryFilter(obj);
    Success(KmsMrkDiscovery(
              KmsMrkAwareDiscovery(
                keyId := "aws-kms-mrk-aware-discovery",
                defaultMrkRegion := defaultMrkRegion,
                awsKmsDiscoveryFilter := awsKmsDiscoveryFilter
              )))
  }

  function ToAwsKmsRsa(key: string, obj: seq<(string, JSON)>)
    : Result<KeyDescription, string>
  {
    var encryptionAlgorithmString :- GetString("encryption-algorithm", obj);
    :- Need(encryptionAlgorithmString in String2EncryptionAlgorithmSpec,
            "Unsupported EncryptionAlgorithmSpec:" + encryptionAlgorithmString);
    var encryptionAlgorithm := String2EncryptionAlgorithmSpec[encryptionAlgorithmString];
    Success(KmsRsa(KmsRsaKeyring( keyId := key, encryptionAlgorithm := encryptionAlgorithm )))
  }

  function ToRawAes(key: string, obj: seq<(string, JSON)>)
    : Result<KeyDescription, string>
  {
    var providerId :- GetString("provider-id", obj);
    Success(AES(RawAES( keyId := key, providerId := providerId )))
  }

  function ToRawRsa(key: string, obj: seq<(string, JSON)>)
    : Result<KeyDescription, string>
  {
    var providerId :- GetString("provider-id", obj);
    var paddingAlgorithm :- GetString("padding-algorithm", obj);

    // In the test vectors the padding-hash for pkcs1 is optional
    var maybePaddingHash :- GetOptionalString("padding-hash", obj);
    :- Need(maybePaddingHash.None? ==> paddingAlgorithm == "pkcs1", "oaep-mgf1 MUST define padding-hash");
    var paddingHash := maybePaddingHash.UnwrapOr("sha1");

    :- Need((paddingAlgorithm, paddingHash) in String2PaddingAlgorithm,
            "Unsupported padding:" + paddingAlgorithm + " hash:" + paddingHash);
    Success(RSA(RawRSA(
                  keyId := key,
                  providerId := providerId,
                  padding := String2PaddingAlgorithm[(paddingAlgorithm, paddingHash)]
                )))
  }

  function ToMultiKeyring(
    json: JSON,
    generatorJson: Option<JSON>,
    childKeyringsJson: seq<JSON>
  )
    : Result<KeyDescription, string>
    requires generatorJson.Some? ==> Size(generatorJson.value) < Size(json)
    requires forall c <- childKeyringsJson :: Size(c) < Size(json)
    decreases Size(json), 0
  {
    :- Need(generatorJson.Some? ==> generatorJson.value.Object?, "Not an object");
    var generator :- if generatorJson.Some? then
                       var g :- ToKeyDescription(generatorJson.value);
                       Success(Some(g))
                     else Success(None);

    var childKeyrings :- Seq.MapWithResult(
                           (c: JSON) requires c in childKeyringsJson =>
                             ToKeyDescription(c),
                           childKeyringsJson);
    Success(Multi(MultiKeyring(
                    generator := generator,
                    childKeyrings := childKeyrings
                  )))
  }

  predicate KeyDescriptionString?(s: string)
  {
    || s == "static-material-keyring"
    || s == "aws-kms"
    || s == "aws-kms-mrk-aware"
    || s == "aws-kms-mrk-aware-discovery"
    || s == "raw"
    || s == "aws-kms-hierarchy"
    || s == "aws-kms-rsa"
    || s == "required-encryption-context-cmm"
    || s == "multi-keyring"
  }

  predicate RawAlgorithmString?(s: string)
  {
    || s == "aes"
    || s == "rsa"
  }

  const String2PaddingAlgorithm := reveal Injective(); Invert(PaddingAlgorithmString2String)

  const PaddingAlgorithmString2String
    := map[
         AwsCryptographyMaterialProvidersTypes.PKCS1 := ("pkcs1", "sha1"),
         AwsCryptographyMaterialProvidersTypes.OAEP_SHA1_MGF1 := ("oaep-mgf1", "sha1"),
         AwsCryptographyMaterialProvidersTypes.OAEP_SHA256_MGF1 := ("oaep-mgf1", "sha256"),
         AwsCryptographyMaterialProvidersTypes.OAEP_SHA384_MGF1 := ("oaep-mgf1", "sha384"),
         AwsCryptographyMaterialProvidersTypes.OAEP_SHA512_MGF1 := ("oaep-mgf1", "sha512")
       ]
  lemma PaddingIsComplete(p: AwsCryptographyMaterialProvidersTypes.PaddingScheme)
    ensures p in PaddingAlgorithmString2String.Keys
  {}

  const String2EncryptionAlgorithmSpec
    := reveal Injective(); Invert(EncryptionAlgorithmSpec2String)
  const EncryptionAlgorithmSpec2String
    := map[
         ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1 := "RSAES_OAEP_SHA_1",
         ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256 := "RSAES_OAEP_SHA_256"
         // SYMMETRIC_DEFAULT is not supported because RSA is asymmetric only
       ]

  type KeyDescriptionVersion = v: nat | KeyDescriptionVersion?(v)  witness 1
  predicate KeyDescriptionVersion?(v: nat)
  {
    || v == 1
    || v == 2
    || v == 3
  }

  function ToJson(
    keyDescription: KeyDescription,
    outputVersion: KeyDescriptionVersion
  ) : (output: Result<JSON, string>)
  {
    match keyDescription
    case Kms(Kms) =>
      Success(Object([
                       ("type", String("aws-kms")),
                       ("key", String(Kms.keyId))
                     ]))
    case KmsMrk(KmsMrk) =>
      Success(Object([
                       ("type", String("aws-kms-mrk-aware")),
                       ("key", String(KmsMrk.keyId))
                     ]))
    case KmsMrkDiscovery(KmsMrkDiscovery) =>
      var filter := if KmsMrkDiscovery.awsKmsDiscoveryFilter.Some? then
                      [("aws-kms-discovery-filter", Object([
                        ("partition", String(KmsMrkDiscovery.awsKmsDiscoveryFilter.value.partition)),
                        ("account-ids", Array(
                        Seq.Map(s => String(s), KmsMrkDiscovery.awsKmsDiscoveryFilter.value.accountIds)))
                        ]))]
                    else
                      [];
      Success(Object([
                       ("type", String("aws-kms-mrk-aware-discovery")),
                       ("default-mrk-region", String(KmsMrkDiscovery.defaultMrkRegion))
                     ] + filter))
    case RSA(RSA) =>
      var padding := (PaddingIsComplete(RSA.padding); PaddingAlgorithmString2String[RSA.padding]);
      Success(Object([
                       ("type", String("raw")),
                       ("key", String(RSA.keyId)),
                       ("provider-id", String(RSA.providerId)),
                       ("encryption-algorithm", String("rsa")),
                       ("padding-algorithm", String(padding.0)),
                       ("padding-hash", String(padding.1))
                     ]))
    case AES(AES) =>
      Success(Object([
                       ("type", String("raw")),
                       ("key", String(AES.keyId)),
                       ("provider-id", String(AES.providerId)),
                       ("encryption-algorithm", String("aes"))
                     ]))
    case Static(Static) =>
      Success(Object([
                       ("type", String("static-material-keyring")),
                       ("key", String(Static.keyId))
                     ]))
    case KmsRsa(KmsRsa) =>
      :- Need(KmsRsa.encryptionAlgorithm in EncryptionAlgorithmSpec2String, "Unsupported encryptionAlgorithm");
      var encryptionAlgorithm := EncryptionAlgorithmSpec2String[KmsRsa.encryptionAlgorithm];
      Success(Object([
                       ("type", String("aws-kms-rsa")),
                       ("key", String(KmsRsa.keyId)),
                       ("encryption-algorithm", String(encryptionAlgorithm))
                     ]))
    case Hierarchy(Hierarchy) =>
      Success(Object([
                       ("type", String("aws-kms-hierarchy")),
                       ("key", String(Hierarchy.keyId))
                     ]))
    case Multi(MultiKeyring) =>
      :- Need(
           && (MultiKeyring.generator.Some? ==> Keyring?(MultiKeyring.generator.value))
           && (forall c <- MultiKeyring.childKeyrings :: Keyring?(c))
         , "CMMs not supported by Multi Keyrings");
      (match outputVersion
       case 3 =>
         var generator :- if MultiKeyring.generator.Some? then
                            var g :- ToJson(MultiKeyring.generator.value, outputVersion);
                            Success(Some(g))
                          else
                            Success(None);
         var childKeyrings :- KeyDescriptionListToJson(MultiKeyring.childKeyrings, outputVersion);
         Success(Object([
                          ("type", String("multi-keyring")),
                          ("childKeyrings", Array(childKeyrings))
                        ]
                        + (if generator.Some?
                           then [("generator", generator.value)] else [])
                 ))
       case _ =>
         :- Need(MultiKeyring.generator.Some?, "Generator required for v1 or v2");
         var keyrings := [MultiKeyring.generator.value] + MultiKeyring.childKeyrings;
         :- Need(forall c <- keyrings :: !c.Multi?, "Recursive structures not supported");
         var keyrings :- KeyDescriptionListToJson(MultiKeyring.childKeyrings, outputVersion);
         Success(Array(keyrings))
      )
    case RequiredEncryptionContext(RequiredEncryptionContext) =>
      var underlying :- ToJson(RequiredEncryptionContext.underlying, outputVersion);
      var requiredEncryptionContextKeys :- Seq.MapWithResult(
                                             key =>
                                               var s :- UTF8.Decode(key);
                                               Success(String(s)),
                                             RequiredEncryptionContext.requiredEncryptionContextKeys);
      Success(Object([
                       ("type", String("required-encryption-context-cmm")),
                       ("underlying", underlying),
                       ("requiredEncryptionContextKeys", Array(requiredEncryptionContextKeys))
                     ]))
  }

  predicate Keyring?(description: KeyDescription)
  {
    || description.Kms?
    || description.KmsMrk?
    || description.KmsMrkDiscovery?
    || description.RSA?
    || description.AES?
    || description.Static?
    || description.KmsRsa?
    || description.Hierarchy?
    || description.Multi?
  }

  function KeyDescriptionListToJson(
    childKeyrings: KeyDescriptionList,
    outputVersion: KeyDescriptionVersion
  ) : (output: Result<seq<JSON>, string>)
  {
    if 0 == |childKeyrings| then
      Success([])
    else
      var json :- ToJson(childKeyrings[0], outputVersion);
      var rest :- KeyDescriptionListToJson(childKeyrings[1..], outputVersion);
      Success([json] + rest)
  }

  function {:opaque} Invert<X(!new), Y(!new)>(m: map<X, Y>): map<Y, X>
    requires Injective(m)
  {
    reveal Injective();
    map k <- m :: m[k] := k
  }

  /* True iff a map is injective. */
  ghost predicate {:opaque} Injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }

}
