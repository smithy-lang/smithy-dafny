// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "TestVectors.dfy"
include "ParseJsonManifests.dfy"
  // TODO it would be nice to have this included somehow...
include "../../KeyVectors/src/Index.dfy"

module {:options "-functionSyntax:4"} TestManifests {
  import Types = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import TestVectors
  import FileIO
  import JSON.API
  import JSON.Values
  import Seq
  import BoundedInts
  import opened JSONHelpers
  import ParseJsonManifests
  import KeyVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  method  {:options "-functionSyntax:4"} StartEncrypt(
    encryptManifestPath: string,
    keysManifiestPath: string
  )
  {
    var encryptManifestBv :- expect FileIO.ReadBytesFromFile(encryptManifestPath);
    var encryptManifestBytes := BvToBytes(encryptManifestBv);
    var encryptManifestJSON :- expect API.Deserialize(encryptManifestBytes);
    expect encryptManifestJSON.Object?;

    var keys :- expect KeyVectors.KeyVectors(KeyVectorsTypes.KeyVectorsConfig(
                                               keyManifiestPath := keysManifiestPath
                                             ));

    var jsonTests :- expect GetObject("tests", encryptManifestJSON.obj);
    var encryptVectors :- expect ParseJsonManifests.BuildEncryptTestVector(keys, jsonTests);

    var encryptTests :- expect ToEncryptTests(keys, encryptVectors);

    var decryptTests := TestEncrypts(encryptTests, keys);
    var _ := TestDecrypts(decryptTests);
  }

  method TestEncrypts(tests: seq<TestVectors.EncryptTest>, keys: KeyVectors.KeyVectorsClient)
    returns (output: seq<TestVectors.DecryptTest>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    requires forall t <- tests :: t.cmm.ValidState()
    modifies set t <- tests, o | o in t.cmm.Modifies :: o
    ensures forall t <- tests :: t.cmm.ValidState()
    ensures forall t <- output ::
              && t.cmm.ValidState()
              && fresh(t.cmm.Modifies)
  {
    var hasFailure := false;

    print "\n=================== Starting Encrypt Tests =================== \n\n";

    var decryptableTests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)> := [];

    for i := 0 to |tests|
      invariant forall t <- tests :: t.cmm.ValidState()
    {
      var test := tests[i];
      var pass, maybeEncryptionMaterials := TestVectors.TestGetEncryptionMaterials(test);

      if pass && test.vector.PositiveEncryptKeyringVector? {
        decryptableTests := decryptableTests + [(test, maybeEncryptionMaterials.value)];
      } else if !pass {
        hasFailure := true;
      }
    }

    print "\n=================== Completed Encrypt Tests =================== \n\n";

    expect !hasFailure;
    output :- expect ToDecryptTests(keys, decryptableTests);
  }

  method TestDecrypts(tests: seq<TestVectors.DecryptTest>)
    returns (manifest: seq<BoundedInts.byte>)
    requires forall t <- tests :: t.cmm.ValidState()
    modifies set t <- tests, o | o in t.cmm.Modifies :: o
    ensures forall t <- tests :: t.cmm.ValidState()
  {

    print "\n=================== Starting Decrypt Tests =================== \n\n";

    var hasFailure := false;

    for i := 0 to |tests|
      invariant forall t <- tests :: t.cmm.ValidState()
    {
      var pass := TestVectors.TestDecryptMaterials(tests[i]);
      if !pass {
        hasFailure := true;
      }
    }
    print "\n=================== Completed Decrypt Tests =================== \n\n";

    expect !hasFailure;

    manifest := ToJSONDecryptManifiest(tests);
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

  method ToDecryptTests(keys: KeyVectors.KeyVectorsClient, tests: seq<(TestVectors.EncryptTest, Types.EncryptionMaterials)>)
    returns (output: Result<seq<TestVectors.DecryptTest>, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && forall t <- output.value ::
                && t.cmm.ValidState()
                && fresh(t.cmm.Modifies)
  {

    var positiveEncryptTests := Seq.Filter(
      (r: (TestVectors.EncryptTest, Types.EncryptionMaterials)) =>
        r.0.vector.PositiveEncryptKeyringVector?,
      tests
    );

    var decryptTests: seq<TestVectors.DecryptTest> := [];
    for i := 0 to |positiveEncryptTests|
      invariant forall t <- decryptTests ::
          && t.cmm.ValidState()
          && fresh(t.cmm.Modifies)
    {
      var test :- TestVectors.ToDecryptTest(keys, positiveEncryptTests[i].0, positiveEncryptTests[i].1);
      decryptTests := decryptTests + [test];
    }

    return Success(decryptTests);
  }

  function ToJSONDecryptManifiest(tests: seq<TestVectors.DecryptTest>)
    : seq<BoundedInts.byte>
  {
    []
  }

}
