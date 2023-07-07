// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
  // Yes, this is reaching across.
  // idealy all these functions would exist in the STD Library.
include "../../TestVectorsAwsCryptographicMaterialProviders/src/JSONHelpers.dfy"

module {:options "-functionSyntax:4"} KeyDescription {
  import opened Wrappers
  import opened JSON.Values
  import AwsCryptographyMaterialProvidersTypes
  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import opened JSONHelpers
  import ComAmazonawsKmsTypes


  function printErr(e: string) : (){()} by method {print e, "\n", "\n"; return ();}
  function printJSON(e: seq<(string, JSON)>) : (){()} by method {print e, "\n", "\n"; return ();}

  function ToKeyDescription(obj: JSON): Result<KeyDescription, string>
  {
    :- Need(obj.Object?, "KeyDescription not an object");
    var obj := obj.obj;
    var typString := "type";
    var typ :- GetString(typString, obj);

    :- Need(KeyDescriptionString?(typ), "Unsupported KeyDescription type:" + typ);

    match typ
    case "aws-kms-mrk-aware-discovery" =>
      var defaultMrkRegion :- GetString("default-mrk-region", obj);
      var filter := GetObject("aws-kms-discovery-filter", obj);
      var awsKmsDiscoveryFilter := ToDiscoveryFilter(obj);
      Success(KmsMrkDiscovery(KmsMrkAwareDiscovery(
                                keyId := "aws-kms-mrk-aware-discovery",
                                defaultMrkRegion := defaultMrkRegion,
                                awsKmsDiscoveryFilter := awsKmsDiscoveryFilter
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
      case "aws-kms-rsa" =>
        var encryptionAlgorithmString :- GetString("encryption-algorithm", obj);
        :- Need(EncryptionAlgorithmSpec?(encryptionAlgorithmString), "Unsupported EncryptionAlgorithmSpec:" + encryptionAlgorithmString);
        var encryptionAlgorithm := match encryptionAlgorithmString
          case "RSAES_OAEP_SHA_1" => ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1
          case "RSAES_OAEP_SHA_256" => ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256;
        Success(KmsRsa(KmsRsaKeyring( keyId := key, encryptionAlgorithm := encryptionAlgorithm )))
      case "aws-kms-hierarchy" =>
        Success(Hierarchy(HierarchyKeyring( keyId := key )))
      case "raw" =>
        var algorithm :- GetString("encryption-algorithm", obj);
        var providerId :- GetString("provider-id", obj);
        :- Need(RawAlgorithmString?(algorithm), "Unsupported algorithm:" + algorithm);
        match algorithm
        case "aes" =>
          Success(AES(RawAES( keyId := key, providerId := providerId )))
        case "rsa" =>
          var paddingAlgorithm :- GetString("padding-algorithm", obj);
          var paddingHash :- GetString("padding-hash", obj);
          :- Need(PaddingAlgorithmString?(paddingAlgorithm), "Unsupported paddingAlgorithm:" + paddingAlgorithm);
          :- Need(PaddingHashString?(paddingHash), "Unsupported paddingHash:" + paddingHash);

          match paddingAlgorithm
          case "pkcs1" =>
            :- Need(paddingHash == "sha1", "Unsupported padding with pkcs1:" + paddingHash);
            Success(RSA(RawRSA( keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.PKCS1 )))
          case "oaep-mgf1" => match paddingHash
            case "sha1" => Success(RSA(RawRSA( keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA1_MGF1 )))
            case "sha256" => Success(RSA(RawRSA( keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA256_MGF1 )))
            case "sha384" => Success(RSA(RawRSA( keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA384_MGF1 )))
            case "sha512" => Success(RSA(RawRSA( keyId := key, providerId := providerId, padding := AwsCryptographyMaterialProvidersTypes.OAEP_SHA512_MGF1 )))
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

  predicate KeyDescriptionString?(s: string)
  {
    || s == "static-material-keyring"
    || s == "aws-kms"
    || s == "aws-kms-mrk-aware"
    || s == "aws-kms-mrk-aware-discovery"
    || s == "raw"
    || s == "aws-kms-hierarchy"
    || s == "aws-kms-rsa"
  }

  predicate RawAlgorithmString?(s: string)
  {
    || s == "aes"
    || s == "rsa"
  }

  predicate PaddingAlgorithmString?(s: string)
  {
    || s == "pkcs1"
    || s == "oaep-mgf1"
  }

  predicate PaddingHashString?(s: string)
  {
    || s == "sha1"
    || s == "sha1"
    || s == "sha256"
    || s == "sha384"
    || s == "sha512"
  }

  predicate EncryptionAlgorithmSpec?(s: string)
  {
    // This is missing SYMMETRIC_DEFAULT because this is asymmetric only
    || s == "RSAES_OAEP_SHA_1"
    || s == "RSAES_OAEP_SHA_256"
  }

}
