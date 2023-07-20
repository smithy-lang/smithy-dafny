// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"

module {:options "/functionSyntax:4" } Structure {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import UTF8


  const BRANCH_KEY_IDENTIFIER_FIELD := "branch-key-id"
  const TYPE_FIELD := "type"
  const KEY_CREATE_TIME := "create-time"
  const HIERARCHY_VERSION := "hierarchy-version"
  const TABLE_FIELD := "tablename"
  const KMS_FIELD := "kms-arn"

  const BRANCH_KEY_FIELD := "enc"
  const BRANCH_KEY_ACTIVE_VERSION_FIELD := "version"

  const BRANCH_KEY_TYPE_PREFIX := "branch:version:"
  const BRANCH_KEY_ACTIVE_TYPE := "branch:ACTIVE"
  const BEACON_KEY_TYPE_VALUE := "beacon:ACTIVE"
  const ENCRYPTION_CONTEXT_PREFIX := "aws-crypto-ec:"

  // A GenerateDataKeyWithoutPlaintext of request size 32 returns a ciphertext size of 184 bytes.
  const KMS_GEN_KEY_NO_PLAINTEXT_LENGTH_32 := 184

  type BranchKeyContext = m: map<string, string> | BranchKeyContext?(m) witness *
  predicate BranchKeyContext?(m: map<string, string>) {
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
    //= type=implication
    //# - MUST have a `branch-key-id` attribute
    && (BRANCH_KEY_IDENTIFIER_FIELD in m)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - MUST have a `type` attribute
    && (TYPE_FIELD in m)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - MUST have a `create-time` attribute
    && (KEY_CREATE_TIME in m)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - MUST have a `hierarchy-version`
    && (HIERARCHY_VERSION in m)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - MUST have a `tablename` attribute to store the logicalKeyStoreName
    && (TABLE_FIELD in m)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - MUST have a `kms-arn` attribute
    && (KMS_FIELD in m)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
    //# The key `enc` MUST NOT exist in the constructed [encryption context](#encryption-context).

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
    //= type=implication
    //# - MUST NOT have a `enc` attribute
    && BRANCH_KEY_FIELD !in m.Keys

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
    //= type=implication
    //# - The `branch-key-id` field MUST not be an empty string
    && 0 < |m[BRANCH_KEY_IDENTIFIER_FIELD]|
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
       //= type=implication
       //# - The `type` field MUST not be an empty string
    && 0 < |m[TYPE_FIELD]|

    && (forall k <- m.Keys :: DDB.IsValid_AttributeName(k))

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#active-encryption-context
    //= type=implication
    //# The ACTIVE encryption context MUST have a `version` attribute.
    && (BRANCH_KEY_ACTIVE_VERSION_FIELD in m <==>
        && m[TYPE_FIELD] == BRANCH_KEY_ACTIVE_TYPE)
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#active-encryption-context
       //= type=implication
       //# The ACTIVE encryption context value of the `type` attribute MUST equal to `"branch:ACTIVE"`.
    && (BRANCH_KEY_ACTIVE_VERSION_FIELD in m ==>
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#active-encryption-context
          //= type=implication
          //# The `version` attribute MUST store the branch key version formatted like `"branch:version:"` + `version`.
          && BRANCH_KEY_TYPE_PREFIX < m[BRANCH_KEY_ACTIVE_VERSION_FIELD])

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#beacon-key-encryption-context
    //= type=implication
    //# The Beacon key encryption context MUST NOT have a `version` attribute.

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#decrypt-only-encryption-context
    //= type=implication
    //# The DECRYPT_ONLY encryption context MUST NOT have a `version` attribute.
    && (BRANCH_KEY_ACTIVE_VERSION_FIELD !in m <==>
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#beacon-key-encryption-context
        //= type=implication
        //# The Beacon key encryption context value of the `type` attribute MUST equal to `"beacon:ACTIVE"`.
        || m[TYPE_FIELD] == BEACON_KEY_TYPE_VALUE
           //= aws-encryption-sdk-specification/framework/branch-key-store.md#decrypt-only-encryption-context
           //= type=implication
           //# The `type` attribute MUST stores the branch key version formatted like `"branch:version:"` + `version`.
        || BRANCH_KEY_TYPE_PREFIX < m[TYPE_FIELD])
  }

  function ToAttributeMap(
    encryptionContext: BranchKeyContext,
    encryptedKey: seq<uint8>
  ): (output: DDB.AttributeMap)
    requires KMS.IsValid_CiphertextType(encryptedKey)
    ensures BranchKeyItem?(output)
    ensures ToBranchKeyContext(output, encryptionContext[TABLE_FIELD]) == encryptionContext
  {
    map k <- encryptionContext.Keys + {BRANCH_KEY_FIELD} - {TABLE_FIELD}
             // Working around https://github.com/dafny-lang/dafny/issues/4214
             //  that will make the following fail to compile
             // ::  match k
             // case HIERARCHY_VERSION => DDB.AttributeValue.N(encryptionContext[HIERARCHY_VERSION])
             // case BRANCH_KEY_FIELD => DDB.AttributeValue.B(encryptedKey)
             // case _ => DDB.AttributeValue.S(encryptionContext[k])
      :: k := if k == HIERARCHY_VERSION then
        DDB.AttributeValue.N(encryptionContext[HIERARCHY_VERSION])
      else if k == BRANCH_KEY_FIELD then
        DDB.AttributeValue.B(encryptedKey)
      else
        DDB.AttributeValue.S(encryptionContext[k])
  }

  function ToBranchKeyContext(
    item: DDB.AttributeMap,
    logicalKeyStoreName: string
  ): (output: BranchKeyContext)
    requires BranchKeyItem?(item)
  {
    map k <- item.Keys - {BRANCH_KEY_FIELD} + {TABLE_FIELD}
             // Working around https://github.com/dafny-lang/dafny/issues/4214
             //  that will make the following fail to compile
             // match k
             // case HIERARCHY_VERSION => item[k].N
             // case TABLE_FIELD => logicalKeyStoreName
             // case _ => item[k].S
      :: k := if k == HIERARCHY_VERSION then
        item[k].N
      else if k == TABLE_FIELD then
        logicalKeyStoreName
      else
        item[k].S
  }

  function ToBranchKeyMaterials(
    encryptionContext: BranchKeyContext,
    plaintextKey: seq<uint8>
  ): (output: Result<Types.BranchKeyMaterials, Types.Error>)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
    //= type=implication
    //# The `type` attribute MUST either be equal to `"branch:ACTIVE"` or start with `"branch:version:"`.
    requires
      || encryptionContext[TYPE_FIELD] == BRANCH_KEY_ACTIVE_TYPE
      || BRANCH_KEY_TYPE_PREFIX < encryptionContext[TYPE_FIELD]

    ensures output.Success?
            ==>
              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
              //= type=implication
              //# - [Branch Key](./structures.md#branch-key) MUST be the [decrypted branch key material](#aws-kms-branch-key-decryption)
              && output.value.branchKey == plaintextKey
                 //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
                 //= type=implication
                 //# - [Branch Key Id](./structures.md#branch-key-id) MUST be the `branch-key-id`
              && output.value.branchKeyIdentifier == encryptionContext[BRANCH_KEY_IDENTIFIER_FIELD]

              && var versionInformation
                   := if BRANCH_KEY_ACTIVE_VERSION_FIELD in encryptionContext then
                        //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
                        //= type=implication
                        //# If the `type` attribute is equal to `"branch:ACTIVE"`
                        //# then the authenticated encryption context MUST have a `version` attribute
                        //# and the version string is this value.
                        encryptionContext[BRANCH_KEY_ACTIVE_VERSION_FIELD]
                      else
                        //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
                        //= type=implication
                        //# If the `type` attribute start with `"branch:version:"` then the version string MUST be equal to this value.
                        encryptionContext[TYPE_FIELD];
              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
              //= type=implication
              //# - [Branch Key Version](./structures.md#branch-key-version)
              //# The version string MUST start with `branch:version:`.
              && BRANCH_KEY_TYPE_PREFIX < versionInformation
              && UTF8.Encode(versionInformation[|BRANCH_KEY_TYPE_PREFIX|..]).Success?
                 //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
                 //= type=implication
                 //# The remaining string encoded as UTF8 bytes MUST be the Branch Key version.
              && output.value.branchKeyVersion == UTF8.Encode(versionInformation[|BRANCH_KEY_TYPE_PREFIX|..]).value

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-materials-from-authenticated-encryption-context
              //= type=implication
              //# - [Encryption Context](./structures.md#encryption-context-3) MUST be constructed by
              //# [Custom Encryption Context From Authenticated Encryption Context](#custom-encryption-context-from-authenticated-encryption-context)
              && ExtractCustomEncryptionContext(encryptionContext).Success?
              && output.value.encryptionContext == ExtractCustomEncryptionContext(encryptionContext).value


  {
    var versionInformation := if BRANCH_KEY_ACTIVE_VERSION_FIELD in encryptionContext then
                                encryptionContext[BRANCH_KEY_ACTIVE_VERSION_FIELD]
                              else
                                encryptionContext[TYPE_FIELD];
    var branchKeyVersion := versionInformation[|BRANCH_KEY_TYPE_PREFIX|..];
    var branchKeyVersionUtf8 :- UTF8.Encode(branchKeyVersion)
                                .MapFailure(e => Types.KeyStoreException( message := e ));

    var customEncryptionContext :- ExtractCustomEncryptionContext(encryptionContext);

    Success(Types.BranchKeyMaterials(
              branchKeyIdentifier := encryptionContext[BRANCH_KEY_IDENTIFIER_FIELD],
              branchKeyVersion := branchKeyVersionUtf8,
              branchKey := plaintextKey,
              encryptionContext := customEncryptionContext
            ))
  }

  function ToBeaconKeyMaterials(
    encryptionContext: BranchKeyContext,
    plaintextKey: seq<uint8>
  ): (output: Result<Types.BeaconKeyMaterials, Types.Error>)
    requires encryptionContext[TYPE_FIELD] == BEACON_KEY_TYPE_VALUE
  {
    var customEncryptionContext :- ExtractCustomEncryptionContext(encryptionContext);

    Success(Types.BeaconKeyMaterials(
              beaconKeyIdentifier := encryptionContext[BRANCH_KEY_IDENTIFIER_FIELD],
              beaconKey := Some(plaintextKey),
              hmacKeys := None,
              encryptionContext := customEncryptionContext
            ))
  }

  function ExtractCustomEncryptionContext(
    encryptionContext: BranchKeyContext
  ): (output: Result<Types.EncryptionContext, Types.Error>)

    ensures
      output.Success?
      ==>
        forall k <- output.value
          ::
            && UTF8.Decode(k).Success?
            && UTF8.Decode(output.value[k]).Success?
               //= aws-encryption-sdk-specification/framework/branch-key-store.md#custom-encryption-context-from-authenticated-encryption-context
               //= type=implication
               //# For every key in the [encryption context](./structures.md#encryption-context-3)
               //# the string `aws-crypto-ec:` + the UTF8 decode of this key
               //# MUST exist as a key in the authenticated encryption context.
            && (ENCRYPTION_CONTEXT_PREFIX + UTF8.Decode(k).value in encryptionContext)
               //= aws-encryption-sdk-specification/framework/branch-key-store.md#custom-encryption-context-from-authenticated-encryption-context
               //= type=implication
               //# Also, the value in the [encryption context](./structures.md#encryption-context-3) for this key
               //# MUST equal the value in the authenticated encryption context
               //# for the constructed key.
            && encryptionContext[ENCRYPTION_CONTEXT_PREFIX + UTF8.Decode(k).value] == UTF8.Decode(output.value[k]).value
  {

    // Dafny needs some help.
    // Adding a fixed string
    // will not make any of the keys collide.
    assert forall k <- encryptionContext.Keys | ENCRYPTION_CONTEXT_PREFIX < k
        ::
          k == ENCRYPTION_CONTEXT_PREFIX + k[|ENCRYPTION_CONTEXT_PREFIX|..];

    var encodedEncryptionContext
      := set k <- encryptionContext
             | ENCRYPTION_CONTEXT_PREFIX < k
           ::
             (UTF8.Encode(k[|ENCRYPTION_CONTEXT_PREFIX|..]), UTF8.Encode(encryptionContext[k]));

    // This SHOULD be impossible
    // A Dafny string SHOULD all be encodable
    :- Need(forall i <- encodedEncryptionContext
              :: i.0.Success? && i.1.Success?,
            Types.KeyStoreException( message :="Unable to encode string"));

    Success(map i <- encodedEncryptionContext :: i.0.value := i.1.value)
  }

  opaque function DecryptOnlyBranchKeyEncryptionContext(
    branchKeyId: string,
    branchKeyVersion: string,
    timestamp: string,
    logicalKeyStoreName: string,
    kmsKeyArn: string,
    customEncryptionContext: map<string, string>
  ): (output: map<string, string>)
    requires 0 < |branchKeyId|
    requires 0 < |branchKeyVersion|
    requires forall k <- customEncryptionContext :: DDB.IsValid_AttributeName(ENCRYPTION_CONTEXT_PREFIX + k)
    ensures BranchKeyContext?(output)
    ensures BRANCH_KEY_TYPE_PREFIX < output[TYPE_FIELD]
    ensures BRANCH_KEY_ACTIVE_VERSION_FIELD !in output
    ensures output[KMS_FIELD] == kmsKeyArn
    ensures output[TABLE_FIELD] == logicalKeyStoreName
    ensures forall k <- customEncryptionContext
              ::
                && ENCRYPTION_CONTEXT_PREFIX + k in output
                && output[ENCRYPTION_CONTEXT_PREFIX + k] == customEncryptionContext[k]

  {
    // Dafny needs some help.
    // Adding a fixed string
    // will not make any of the keys collide.
    // However, this leaks a lot of complexity.
    // This is why the function is now opaque.
    // Otherwise things timeout
    assert forall k <- customEncryptionContext.Keys
        ::
          k == (ENCRYPTION_CONTEXT_PREFIX + k)[|ENCRYPTION_CONTEXT_PREFIX|..];

    map[
      BRANCH_KEY_IDENTIFIER_FIELD := branchKeyId,
      TYPE_FIELD := BRANCH_KEY_TYPE_PREFIX + branchKeyVersion,
      KEY_CREATE_TIME := timestamp,
      TABLE_FIELD := logicalKeyStoreName,
      KMS_FIELD := kmsKeyArn,
      HIERARCHY_VERSION := "1"
    ] + map k <- customEncryptionContext :: ENCRYPTION_CONTEXT_PREFIX + k := customEncryptionContext[k]
  }

  function ActiveBranchKeyEncryptionContext(
    decryptOnlyEncryptionContext: map<string, string>
  ): (output: map<string, string>)
    requires BranchKeyContext?(decryptOnlyEncryptionContext)
    requires
      && BRANCH_KEY_TYPE_PREFIX < decryptOnlyEncryptionContext[TYPE_FIELD]
      && BRANCH_KEY_ACTIVE_VERSION_FIELD !in decryptOnlyEncryptionContext
    ensures BranchKeyContext?(output)
    ensures BRANCH_KEY_ACTIVE_VERSION_FIELD in output
  {
    decryptOnlyEncryptionContext + map[
      BRANCH_KEY_ACTIVE_VERSION_FIELD := decryptOnlyEncryptionContext[TYPE_FIELD],
      TYPE_FIELD := BRANCH_KEY_ACTIVE_TYPE
    ]
  }

  function BeaconKeyEncryptionContext(
    decryptOnlyEncryptionContext: map<string, string>
  ): (output: map<string, string>)
    requires BranchKeyContext?(decryptOnlyEncryptionContext)
    requires
      && BRANCH_KEY_TYPE_PREFIX < decryptOnlyEncryptionContext[TYPE_FIELD]
      && BRANCH_KEY_ACTIVE_VERSION_FIELD !in decryptOnlyEncryptionContext
    ensures BranchKeyContext?(output)
    ensures output[TYPE_FIELD] == BEACON_KEY_TYPE_VALUE
  {
    decryptOnlyEncryptionContext + map[
      TYPE_FIELD := BEACON_KEY_TYPE_VALUE
    ]
  }

  function NewVersionFromActiveBranchKeyEncryptionContext(
    activeBranchKeyEncryptionContext: map<string, string>,
    branchKeyVersion: string,
    timestamp: string
  ): (output: map<string, string>)
    requires BranchKeyContext?(activeBranchKeyEncryptionContext)
    requires BRANCH_KEY_ACTIVE_VERSION_FIELD in activeBranchKeyEncryptionContext
    requires 0 < |branchKeyVersion|

    ensures BranchKeyContext?(output)
    ensures BRANCH_KEY_TYPE_PREFIX < output[TYPE_FIELD]
    ensures BRANCH_KEY_ACTIVE_VERSION_FIELD !in output
  {
    activeBranchKeyEncryptionContext
    + map[
      TYPE_FIELD := BRANCH_KEY_TYPE_PREFIX + branchKeyVersion,
      KEY_CREATE_TIME := timestamp
    ]
    - {BRANCH_KEY_ACTIVE_VERSION_FIELD}
  }


  type BranchKeyItem = m: DDB.AttributeMap | BranchKeyItem?(m) witness *
  //= aws-encryption-sdk-specification/framework/branch-key-store.md#record-format
  //= type=implication
  //# A branch key record MAY include [custom encryption context](#custom-encryption-context) key-value pairs.

  //= aws-encryption-sdk-specification/framework/branch-key-store.md#record-format
  //= type=implication
  //# A branch key record MUST include the following key-value pairs:
  predicate BranchKeyItem?(m: DDB.AttributeMap) {
    && BRANCH_KEY_IDENTIFIER_FIELD in m && m[BRANCH_KEY_IDENTIFIER_FIELD].S?
    && TYPE_FIELD in m && m[TYPE_FIELD].S?
    && KEY_CREATE_TIME in m && m[KEY_CREATE_TIME].S?
    && HIERARCHY_VERSION in m && m[HIERARCHY_VERSION].N?
    && TABLE_FIELD !in m
    && KMS_FIELD in m && m[KMS_FIELD].S?
    && BRANCH_KEY_FIELD in m && m[BRANCH_KEY_FIELD].B?

    && 0 < |m[BRANCH_KEY_IDENTIFIER_FIELD].S|
    && 0 < |m[TYPE_FIELD].S|

    && (forall k <- m.Keys - {BRANCH_KEY_FIELD, HIERARCHY_VERSION} :: m[k].S?)

    && (BRANCH_KEY_ACTIVE_VERSION_FIELD in m <==>
        && m[TYPE_FIELD].S == BRANCH_KEY_ACTIVE_TYPE)
    && (BRANCH_KEY_ACTIVE_VERSION_FIELD in m ==>
          && BRANCH_KEY_TYPE_PREFIX < m[BRANCH_KEY_ACTIVE_VERSION_FIELD].S)

    && (BRANCH_KEY_ACTIVE_VERSION_FIELD !in m <==>
        || m[TYPE_FIELD].S == BEACON_KEY_TYPE_VALUE
        || BRANCH_KEY_TYPE_PREFIX < m[TYPE_FIELD].S)

    && KMS.IsValid_CiphertextType(m[BRANCH_KEY_FIELD].B)
  }

  type ActiveBranchKeyItem = m: DDB.AttributeMap | ActiveBranchKeyItem?(m) witness *
  predicate ActiveBranchKeyItem?(m: DDB.AttributeMap) {
    && BranchKeyItem?(m)
    && m[TYPE_FIELD].S == BRANCH_KEY_ACTIVE_TYPE
    && BRANCH_KEY_ACTIVE_VERSION_FIELD in m && m[BRANCH_KEY_ACTIVE_VERSION_FIELD].S?
    && BRANCH_KEY_TYPE_PREFIX < m[BRANCH_KEY_ACTIVE_VERSION_FIELD].S
  }

  type VersionBranchKeyItem = m: DDB.AttributeMap | VersionBranchKeyItem?(m) witness *
  predicate VersionBranchKeyItem?(m: DDB.AttributeMap) {
    && BranchKeyItem?(m)
    && BRANCH_KEY_ACTIVE_VERSION_FIELD !in m
    && BRANCH_KEY_TYPE_PREFIX < m[TYPE_FIELD].S
  }

  type BeaconKeyItem = m: DDB.AttributeMap | BeaconKeyItem?(m) witness *
  predicate BeaconKeyItem?(m: DDB.AttributeMap) {
    && BranchKeyItem?(m)
    && BRANCH_KEY_ACTIVE_VERSION_FIELD !in m
    && m[TYPE_FIELD].S == BEACON_KEY_TYPE_VALUE
  }

  lemma BranchKeyItemsDoNotCollide(a: ActiveBranchKeyItem, b: VersionBranchKeyItem, c: BeaconKeyItem)
    requires a[BRANCH_KEY_IDENTIFIER_FIELD] == b[BRANCH_KEY_IDENTIFIER_FIELD] == c[BRANCH_KEY_IDENTIFIER_FIELD]
    ensures a[TYPE_FIELD] != b[TYPE_FIELD]
    ensures a[TYPE_FIELD] != c[TYPE_FIELD]
    ensures c[TYPE_FIELD] != b[TYPE_FIELD]
  {}

  lemma ToAttributeMapIsCorrect(
    encryptionContext: BranchKeyContext,
    encryptedKey: seq<uint8>,
    item: DDB.AttributeMap
  )
    requires KMS.IsValid_CiphertextType(encryptedKey)
    requires item == ToAttributeMap(encryptionContext, encryptedKey)

    ensures item.Keys == encryptionContext.Keys + {BRANCH_KEY_FIELD} - {TABLE_FIELD}
    ensures item[BRANCH_KEY_FIELD].B == encryptedKey
    ensures
      && (forall k <- item.Keys - {BRANCH_KEY_FIELD, HIERARCHY_VERSION}
            ::
              && item[k].S?
              && encryptionContext[k] == item[k].S
         )
      && encryptionContext[HIERARCHY_VERSION] == item[HIERARCHY_VERSION].N
  {}

  lemma ToBranchKeyContextIsCorrect(
    encryptionContext: map<string, string>,
    logicalKeyStoreName: string,
    item: DDB.AttributeMap
  )
    requires BranchKeyItem?(item)
    requires encryptionContext == ToBranchKeyContext(item, logicalKeyStoreName)

    ensures encryptionContext.Keys == item.Keys - {BRANCH_KEY_FIELD} + {TABLE_FIELD}
    ensures encryptionContext[TABLE_FIELD] == logicalKeyStoreName

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
    //= type=implication
    //# Every key in the constructed [encryption context](#encryption-context)
    //# except `tableName`
    //# MUST exist as a string attribute in the AWS DDB response item.
    ensures
      forall k <- encryptionContext.Keys - {BRANCH_KEY_FIELD, TABLE_FIELD}
        ::
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
          //= type=implication
          //# Every value in the constructed [encryption context](#encryption-context)
          //# except the logical table name
          //# MUST equal the value with the same key in the AWS DDB response item.

          // Working around https://github.com/dafny-lang/dafny/issues/4214
          //  that will make the following fail to compile
          // match k
          // case HIERARCHY_VERSION => encryptionContext[k] == item[k].N
          // case _ => encryptionContext[k] == item[k].S
          if k == HIERARCHY_VERSION then
            encryptionContext[k] == item[k].N
          else
            encryptionContext[k] == item[k].S

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
    //= type=implication
    //# The key `enc` MUST NOT exist in the constructed [encryption context](#encryption-context).
    ensures BRANCH_KEY_FIELD !in encryptionContext
  {}

  lemma EncryptionContextConstructorsAreCorrect(
    branchKeyId: string,
    branchKeyVersion: string,
    timestamp: string,
    logicalKeyStoreName: string,
    kmsKeyArn: string,
    encryptionContext: map<string, string>
  )
    requires 0 < |branchKeyId|
    requires 0 < |branchKeyVersion|
    requires forall k <- encryptionContext :: DDB.IsValid_AttributeName(ENCRYPTION_CONTEXT_PREFIX + k)

    ensures
      var decryptOnly := DecryptOnlyBranchKeyEncryptionContext(
                           branchKeyId, branchKeyVersion, timestamp, logicalKeyStoreName, kmsKeyArn, encryptionContext);
      var active := ActiveBranchKeyEncryptionContext(decryptOnly);
      var beacon := BeaconKeyEncryptionContext(decryptOnly);
      && decryptOnly[TYPE_FIELD] != active[TYPE_FIELD]
      && decryptOnly[TYPE_FIELD] != beacon[TYPE_FIELD]
      && active[TYPE_FIELD] != beacon[TYPE_FIELD]
      && (forall k <- decryptOnly.Keys - {TYPE_FIELD} ::
            && decryptOnly[k] == active[k] == beacon[k]
         )
      && active[BRANCH_KEY_ACTIVE_VERSION_FIELD] == decryptOnly[TYPE_FIELD]
         //= aws-encryption-sdk-specification/framework/branch-key-store.md#custom-encryption-context
         //= type=implication
         //# If custom [encryption context](./structures.md#encryption-context-3)
         //# is associated with the branch key these values MUST be added to the AWS KMS encryption context.
      && (forall k <- encryptionContext ::
            //= aws-encryption-sdk-specification/framework/branch-key-store.md#custom-encryption-context
            //= type=implication
            //# To avoid name collisions each added attribute from the custom [encryption context](./structures.md#encryption-context-3)
            //# MUST be prefixed with `aws-crypto-ec:`.
            && (ENCRYPTION_CONTEXT_PREFIX + k in decryptOnly)
            && (ENCRYPTION_CONTEXT_PREFIX + k in active)
            && (ENCRYPTION_CONTEXT_PREFIX + k in beacon)
               //= aws-encryption-sdk-specification/framework/branch-key-store.md#custom-encryption-context
               //= type=implication
               //# The added values MUST be equal.
            && encryptionContext[k]
            == decryptOnly[ENCRYPTION_CONTEXT_PREFIX + k]
            == active[ENCRYPTION_CONTEXT_PREFIX + k]
            == beacon[ENCRYPTION_CONTEXT_PREFIX + k]
         )
  {
    reveal DecryptOnlyBranchKeyEncryptionContext();
  }

  lemma ToAttributeMapAndToBranchKeyContextAreInverse(
    encryptionContext: map<string, string>,
    item: DDB.AttributeMap
  )
    requires BranchKeyItem?(item) && BranchKeyContext?(encryptionContext)
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#encryption-context
    //= type=implication
    //# Any additionally attributes on the DynamoDB item
    //# MUST be added to the encryption context.
    ensures
      item == ToAttributeMap(encryptionContext, item[BRANCH_KEY_FIELD].B)
      <==>
      ToBranchKeyContext(item, encryptionContext[TABLE_FIELD]) == encryptionContext
  {}

}
