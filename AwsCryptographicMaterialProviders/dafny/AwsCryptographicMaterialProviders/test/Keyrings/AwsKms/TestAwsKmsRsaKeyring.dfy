// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../../src/Index.dfy"
include "../../../src/Keyrings/AwsKms/AwsKmsDiscoveryKeyring.dfy"
include "../../TestUtils.dfy"
include "../../../../../../ComAmazonawsKms/src/Index.dfy"

module TestAwsKmsRsaKeyring {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import MaterialProviders
  import Types = AwsCryptographyMaterialProvidersTypes
  import AwsKmsRsaKeyring
  import TestUtils
  import ComAmazonawsKmsTypes
  import AlgorithmSuites
  import UTF8

  method {:test} TestKmsRsaRoundtrip() {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var publicKey :- expect UTF8.Encode(TestUtils.KMS_RSA_PUBLIC_KEY);

    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region:="us-west-2"));

    var kmsRsaKeyring :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(
                                                             publicKey := Some(publicKey),
                                                             kmsKeyId := TestUtils.KMS_RSA_PRIVATE_KEY_ARN,
                                                             encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1,
                                                             kmsClient := Some(kmsClient),
                                                             grantTokens := None()
                                                           ));

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var algorithmSuiteId := Types.AlgorithmSuiteId.ESDK(Types.ALG_AES_256_GCM_IV12_TAG16_NO_KDF);
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := [],
        signingKey := None,
        verificationKey := None
      )
    );

    var encryptionMaterialsOut :- expect kmsRsaKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );

    var _ :- expect mpl.EncryptionMaterialsHasPlaintextDataKey(encryptionMaterialsOut.materials);

    expect |encryptionMaterialsOut.materials.encryptedDataKeys| == 1;

    var edk := encryptionMaterialsOut.materials.encryptedDataKeys[0];

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionContext,
        requiredEncryptionContextKeys := []
      )
    );
    var decryptionMaterialsOut :- expect kmsRsaKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[edk]
      )
    );

    expect encryptionMaterialsOut.materials.plaintextDataKey
        == decryptionMaterialsOut.materials.plaintextDataKey;
  }

  method {:test} TestKmsRsaWithAsymmetricSignatureFails() {
    var mpl :- expect MaterialProviders.MaterialProviders();

    var publicKey :- expect UTF8.Encode(TestUtils.KMS_RSA_PUBLIC_KEY);

    var clientSupplier :- expect mpl.CreateDefaultClientSupplier(Types.CreateDefaultClientSupplierInput());
    var kmsClient :- expect clientSupplier.GetClient(Types.GetClientInput(region:="us-west-2"));

    var kmsRsaKeyring :- expect mpl.CreateAwsKmsRsaKeyring(Types.CreateAwsKmsRsaKeyringInput(
                                                             publicKey := Some(publicKey),
                                                             kmsKeyId := TestUtils.KMS_RSA_PRIVATE_KEY_ARN,
                                                             encryptionAlgorithm := ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1,
                                                             kmsClient := Some(kmsClient),
                                                             grantTokens := None()
                                                           ));

    var algorithmSuiteId := Types.AlgorithmSuiteId.DBE(Types.ALG_AES_256_GCM_HKDF_SHA512_COMMIT_KEY_ECDSA_P384_SYMSIG_HMAC_SHA384);
    var suite := AlgorithmSuites.GetSuite(algorithmSuiteId);
    var encryptionMaterialsIn :- expect mpl.InitializeEncryptionMaterials(
      Types.InitializeEncryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := map[],
        requiredEncryptionContextKeys := [],
        signingKey := Some([0,0,0,0,0]),
        verificationKey := Some([0,0,0,0,0])
      )
    );

    var encryptionMaterialsOutRes := kmsRsaKeyring.OnEncrypt(
      Types.OnEncryptInput(materials:=encryptionMaterialsIn)
    );

    expect encryptionMaterialsOutRes.Failure?;
    expect encryptionMaterialsOutRes.error.AwsCryptographicMaterialProvidersException?;
    expect encryptionMaterialsOutRes.error.message == "AwsKmsRsaKeyring cannot be used with" +
                                                      " an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing.";

    var decryptionMaterialsIn :- expect mpl.InitializeDecryptionMaterials(
      Types.InitializeDecryptionMaterialsInput(
        algorithmSuiteId := algorithmSuiteId,
        encryptionContext := encryptionMaterialsIn.encryptionContext,
        requiredEncryptionContextKeys := []
      )
    );
    var decryptionMaterialsOutRes := kmsRsaKeyring.OnDecrypt(
      Types.OnDecryptInput(
        materials:=decryptionMaterialsIn,
        encryptedDataKeys:=[]
      )
    );

    expect decryptionMaterialsOutRes.Failure?;
    expect decryptionMaterialsOutRes.error.AwsCryptographicMaterialProvidersException?;
    expect decryptionMaterialsOutRes.error.message == "AwsKmsRsaKeyring cannot be used with" +
                                                      " an Algorithm Suite with asymmetric signing. Please specify an algorithm suite without asymmetric signing.";
  }
}
