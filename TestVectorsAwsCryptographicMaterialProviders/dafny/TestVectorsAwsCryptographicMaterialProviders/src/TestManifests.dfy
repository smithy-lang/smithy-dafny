// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "TestVectors.dfy"
include "ParseJsonManifests.dfy"
include "MplManifestOptions.dfy"
  // TODO it would be nice to have this included somehow...
include "../../KeyVectors/src/Index.dfy"

module {:options "-functionSyntax:4"} TestManifests {
  import Types = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import Aws.Cryptography.Primitives
  import TestVectors
  import FileIO
  import JSON.API
  import JSON.Values
  import JSON.Errors
  import Seq
  import BoundedInts
  import opened JSONHelpers
  import ParseJsonManifests
  import KeyVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import MplManifestOptions
  import CompleteVectors

  method StartEncrypt(op: MplManifestOptions.ManifestOptions)
    returns (output: Result<(), string>)
    requires op.Encrypt?
  {
    var encryptManifest :- GetManifest(op.manifestPath, "manifest.json");
    :- Need(encryptManifest.EncryptManifest?, "Not a encrypt manifest");

    var encryptVectors :- ParseJsonManifests.BuildEncryptTestVector(encryptManifest.keys, encryptManifest.jsonTests);
    var encryptTests :- ToEncryptTests(encryptManifest.keys, encryptVectors);
    var decryptVectors := TestEncrypts(encryptTests, encryptManifest.keys);

    var _ :- CompleteVectors.WriteDecryptManifest(op, encryptManifest.keys, decryptVectors);

    output := Success(());
  }

  method TestEncrypts(tests: seq<TestVectors.EncryptTest>, keys: KeyVectors.KeyVectorsClient)
    returns (output: seq<TestVectors.DecryptTestVector>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    requires forall t <- tests :: t.cmm.ValidState()
    modifies set t <- tests, o | o in t.cmm.Modifies :: o
    ensures forall t <- tests :: t.cmm.ValidState()
  {
    var hasFailure := false;

    print "\n=================== Starting ", |tests|, " Encrypt Tests =================== \n\n";

    var decryptableTests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)> := [];

    for i := 0 to |tests|
      invariant forall t <- tests :: t.cmm.ValidState()
    {
      var test := tests[i];
      var pass, maybeEncryptionMaterials := TestVectors.TestGetEncryptionMaterials(test);

      if pass && !test.vector.NegativeEncryptKeyringVector? {
        decryptableTests := decryptableTests + [(test, maybeEncryptionMaterials.value)];
      } else if !pass {
        hasFailure := true;
      }
    }

    print "\n=================== Completed ", |tests|, " Encrypt Tests =================== \n\n";

    expect !hasFailure;
    output :- expect ToDecryptTestVectors(keys, decryptableTests);
  }

  method StartDecrypt(op: MplManifestOptions.ManifestOptions)
    returns (output: Result<(), string>)
    requires op.Decrypt?
  {
    var decryptManifest :- GetManifest(op.manifestPath, "manifest.json");
    :- Need(decryptManifest.DecryptManifest?, "Not a encrypt manifest");

    var decryptVectors :- ParseJsonManifests.BuildDecryptTestVector(decryptManifest.keys, decryptManifest.jsonTests);
    var decryptTests :- ToDecryptTests(decryptManifest.keys, decryptVectors);

    TestDecrypts(decryptTests);

    output := Success(());
  }

  method TestDecrypts(tests: seq<TestVectors.DecryptTest>)
    requires forall t <- tests :: t.cmm.ValidState()
    modifies set t <- tests, o | o in t.cmm.Modifies :: o
    ensures forall t <- tests :: t.cmm.ValidState()
  {

    print "\n=================== Starting ", |tests|, " Decrypt Tests =================== \n\n";

    var hasFailure := false;

    for i := 0 to |tests|
      invariant forall t <- tests :: t.cmm.ValidState()
    {
      var pass := TestVectors.TestDecryptMaterials(tests[i]);
      if !pass {
        hasFailure := true;
      }
    }
    print "\n=================== Completed ", |tests|, " Decrypt Tests =================== \n\n";

    expect !hasFailure;
  }

  method ToEncryptTests(keys: KeyVectors.KeyVectorsClient, encryptVectors: seq<TestVectors.EncryptTestVector>)
    returns (output: Result<seq<TestVectors.EncryptTest>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && forall t <- output.value ::
                && t.cmm.ValidState()
                && fresh(t.cmm.Modifies)
  {
    var encryptTests: seq<TestVectors.EncryptTest> := [];
    for i := 0 to |encryptVectors|
      invariant forall t <- encryptTests ::
          && t.cmm.ValidState()
          && fresh(t.cmm.Modifies)
    {
      var test :- TestVectors.ToEncryptTest(keys, encryptVectors[i]);
      encryptTests := encryptTests + [test];
    }

    return Success(encryptTests);
  }

  method ToDecryptTestVectors(keys: KeyVectors.KeyVectorsClient, tests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)>)
    returns (output: Result<seq<TestVectors.DecryptTestVector>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
  {

    var successfulEncrypt := Seq.Filter(
      (r: (TestVectors.EncryptTest, Types.EncryptionMaterials)) =>
        r.0.vector.PositiveEncryptKeyringVector? || r.0.vector.PositiveEncryptNegativeDecryptKeyringVector?,
      tests
    );

    var decryptTestVectors: seq<TestVectors.DecryptTestVector> := [];
    for i := 0 to |successfulEncrypt|
    {
      var vector := TestVectors.EncryptTestToDecryptVector(successfulEncrypt[i].0, successfulEncrypt[i].1);
      decryptTestVectors := decryptTestVectors + [vector];
    }

    output := Success(decryptTestVectors);
  }


  method ToDecryptTests(keys: KeyVectors.KeyVectorsClient, vectors: seq<TestVectors.DecryptTestVector>)
    returns (output: Result<seq<TestVectors.DecryptTest>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && forall t <- output.value ::
                && t.cmm.ValidState()
                && fresh(t.cmm.Modifies)
  {
    var decryptTests: seq<TestVectors.DecryptTest> := [];
    for i := 0 to |vectors|
      invariant forall t <- decryptTests ::
          && t.cmm.ValidState()
          && fresh(t.cmm.Modifies)
    {
      var test :- TestVectors.DecryptVectorToDecryptTest(keys, vectors[i]);
      decryptTests := decryptTests + [test];
    }

    return Success(decryptTests);
  }

  datatype ManifestData =
    | DecryptManifest(
        version: nat,
        keys: KeyVectors.KeyVectorsClient,
        client: Values.JSON,
        jsonTests: seq<(string, Values.JSON)>
      )
    | EncryptManifest(
        version: nat,
        keys: KeyVectors.KeyVectorsClient,
        jsonTests: seq<(string, Values.JSON)>
      )

  method GetManifest(
    manifestPath: string,
    manifestFileName: string
  )
    returns (manifestData: Result<ManifestData, string>)

    ensures manifestData.Success? ==>
              && fresh(manifestData.value.keys.Modifies)
              && manifestData.value.keys.ValidState()
  {
    var decryptManifestBv :- FileIO.ReadBytesFromFile(manifestPath + manifestFileName);
    var decryptManifestBytes := BvToBytes(decryptManifestBv);
    var manifestJson :- API.Deserialize(decryptManifestBytes)
    .MapFailure(( e: Errors.DeserializationError ) => e.ToString());
    :- Need(manifestJson.Object?, "Not a JSON object");

    var manifest :- GetObject("manifest", manifestJson.obj);
    var version :- GetNat("version", manifest);
    var typ :- GetString("type", manifest);

    var keyManifestUri :- GetString("keys", manifestJson.obj);
    :- Need("file://" < keyManifestUri, "Unexpected URI prefix");
    var keyManifestPath := manifestPath + keyManifestUri[7..];
    var keys :- expect KeyVectors.KeyVectors(KeyVectorsTypes.KeyVectorsConfig(
                                               keyManifestPath := keyManifestPath
                                             ));

    var jsonTests :- GetObject("tests", manifestJson.obj);

    match typ
    case "awses-mpl-decrypt" =>
      var client :- Get("client", manifestJson.obj);
      manifestData := Success(DecryptManifest(
                                version := version,
                                keys := keys,
                                client := client,
                                jsonTests := jsonTests
                              ));

    case "awses-mpl-encrypt" =>
      manifestData := Success(EncryptManifest(
                                version := version,
                                keys := keys,
                                jsonTests := jsonTests
                              ));

    case _ =>
      manifestData := Failure("Unsupported manifest type:" + typ);
  }

}
