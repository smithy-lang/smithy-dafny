// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be
// overwritten.
package software.amazon.cryptography.keystore;

import Wrappers_Compile.Option;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import software.amazon.cryptography.keystore.internaldafny.types.BeaconKeyMaterials;
import software.amazon.cryptography.keystore.internaldafny.types.BranchKeyMaterials;
import software.amazon.cryptography.keystore.internaldafny.types.CreateKeyInput;
import software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput;
import software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput;
import software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput;
import software.amazon.cryptography.keystore.internaldafny.types.Error;
import software.amazon.cryptography.keystore.internaldafny.types.Error_KeyStoreException;
import software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput;
import software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput;
import software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput;
import software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput;
import software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput;
import software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput;
import software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput;
import software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient;
import software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration;
import software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig;
import software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput;
import software.amazon.cryptography.keystore.internaldafny.types.VersionKeyOutput;
import software.amazon.cryptography.keystore.model.CollectionOfErrors;
import software.amazon.cryptography.keystore.model.KeyStoreException;
import software.amazon.cryptography.keystore.model.OpaqueError;
import software.amazon.cryptography.services.dynamodb.internaldafny.types.IDynamoDBClient;
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;

public class ToDafny {

  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof KeyStoreException) {
      return ToDafny.Error((KeyStoreException) nativeValue);
    }
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list =
      software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(),
        ToDafny::Error,
        Error._typeDescriptor()
      );
    DafnySequence<? extends Character> message =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.getMessage()
      );
    return Error.create_CollectionOfErrors(list, message);
  }

  public static BeaconKeyMaterials BeaconKeyMaterials(
    software.amazon.cryptography.keystore.model.BeaconKeyMaterials nativeValue
  ) {
    DafnySequence<? extends Character> beaconKeyIdentifier;
    beaconKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.beaconKeyIdentifier()
      );
    DafnyMap<
      ? extends DafnySequence<? extends Byte>,
      ? extends DafnySequence<? extends Byte>
    > encryptionContext;
    encryptionContext =
      ToDafny.EncryptionContext(nativeValue.encryptionContext());
    Option<DafnySequence<? extends Byte>> beaconKey;
    beaconKey =
      Objects.nonNull(nativeValue.beaconKey())
        ? Option.create_Some(
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.beaconKey()
          )
        )
        : Option.create_None();
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Byte>
      >
    > hmacKeys;
    hmacKeys =
      (Objects.nonNull(nativeValue.hmacKeys()) &&
          nativeValue.hmacKeys().size() > 0)
        ? Option.create_Some(ToDafny.HmacKeyMap(nativeValue.hmacKeys()))
        : Option.create_None();
    return new BeaconKeyMaterials(
      beaconKeyIdentifier,
      encryptionContext,
      beaconKey,
      hmacKeys
    );
  }

  public static BranchKeyMaterials BranchKeyMaterials(
    software.amazon.cryptography.keystore.model.BranchKeyMaterials nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    DafnySequence<? extends Byte> branchKeyVersion;
    branchKeyVersion =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(
        nativeValue.branchKeyVersion()
      );
    DafnyMap<
      ? extends DafnySequence<? extends Byte>,
      ? extends DafnySequence<? extends Byte>
    > encryptionContext;
    encryptionContext =
      ToDafny.EncryptionContext(nativeValue.encryptionContext());
    DafnySequence<? extends Byte> branchKey;
    branchKey =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
        nativeValue.branchKey()
      );
    return new BranchKeyMaterials(
      branchKeyIdentifier,
      branchKeyVersion,
      encryptionContext,
      branchKey
    );
  }

  public static CreateKeyInput CreateKeyInput(
    software.amazon.cryptography.keystore.model.CreateKeyInput nativeValue
  ) {
    Option<DafnySequence<? extends Character>> branchKeyIdentifier;
    branchKeyIdentifier =
      Objects.nonNull(nativeValue.branchKeyIdentifier())
        ? Option.create_Some(
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.branchKeyIdentifier()
          )
        )
        : Option.create_None();
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Byte>,
        ? extends DafnySequence<? extends Byte>
      >
    > encryptionContext;
    encryptionContext =
      (Objects.nonNull(nativeValue.encryptionContext()) &&
          nativeValue.encryptionContext().size() > 0)
        ? Option.create_Some(
          ToDafny.EncryptionContext(nativeValue.encryptionContext())
        )
        : Option.create_None();
    return new CreateKeyInput(branchKeyIdentifier, encryptionContext);
  }

  public static CreateKeyOutput CreateKeyOutput(
    software.amazon.cryptography.keystore.model.CreateKeyOutput nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    return new CreateKeyOutput(branchKeyIdentifier);
  }

  public static CreateKeyStoreInput CreateKeyStoreInput(
    software.amazon.cryptography.keystore.model.CreateKeyStoreInput nativeValue
  ) {
    return new CreateKeyStoreInput();
  }

  public static CreateKeyStoreOutput CreateKeyStoreOutput(
    software.amazon.cryptography.keystore.model.CreateKeyStoreOutput nativeValue
  ) {
    DafnySequence<? extends Character> tableArn;
    tableArn =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.tableArn()
      );
    return new CreateKeyStoreOutput(tableArn);
  }

  public static GetActiveBranchKeyInput GetActiveBranchKeyInput(
    software.amazon.cryptography.keystore.model.GetActiveBranchKeyInput nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    return new GetActiveBranchKeyInput(branchKeyIdentifier);
  }

  public static GetActiveBranchKeyOutput GetActiveBranchKeyOutput(
    software.amazon.cryptography.keystore.model.GetActiveBranchKeyOutput nativeValue
  ) {
    BranchKeyMaterials branchKeyMaterials;
    branchKeyMaterials =
      ToDafny.BranchKeyMaterials(nativeValue.branchKeyMaterials());
    return new GetActiveBranchKeyOutput(branchKeyMaterials);
  }

  public static GetBeaconKeyInput GetBeaconKeyInput(
    software.amazon.cryptography.keystore.model.GetBeaconKeyInput nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    return new GetBeaconKeyInput(branchKeyIdentifier);
  }

  public static GetBeaconKeyOutput GetBeaconKeyOutput(
    software.amazon.cryptography.keystore.model.GetBeaconKeyOutput nativeValue
  ) {
    BeaconKeyMaterials beaconKeyMaterials;
    beaconKeyMaterials =
      ToDafny.BeaconKeyMaterials(nativeValue.beaconKeyMaterials());
    return new GetBeaconKeyOutput(beaconKeyMaterials);
  }

  public static GetBranchKeyVersionInput GetBranchKeyVersionInput(
    software.amazon.cryptography.keystore.model.GetBranchKeyVersionInput nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    DafnySequence<? extends Character> branchKeyVersion;
    branchKeyVersion =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyVersion()
      );
    return new GetBranchKeyVersionInput(branchKeyIdentifier, branchKeyVersion);
  }

  public static GetBranchKeyVersionOutput GetBranchKeyVersionOutput(
    software.amazon.cryptography.keystore.model.GetBranchKeyVersionOutput nativeValue
  ) {
    BranchKeyMaterials branchKeyMaterials;
    branchKeyMaterials =
      ToDafny.BranchKeyMaterials(nativeValue.branchKeyMaterials());
    return new GetBranchKeyVersionOutput(branchKeyMaterials);
  }

  public static GetKeyStoreInfoOutput GetKeyStoreInfoOutput(
    software.amazon.cryptography.keystore.model.GetKeyStoreInfoOutput nativeValue
  ) {
    DafnySequence<? extends Character> keyStoreId;
    keyStoreId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyStoreId()
      );
    DafnySequence<? extends Character> keyStoreName;
    keyStoreName =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyStoreName()
      );
    DafnySequence<? extends Character> logicalKeyStoreName;
    logicalKeyStoreName =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.logicalKeyStoreName()
      );
    DafnySequence<? extends DafnySequence<? extends Character>> grantTokens;
    grantTokens = ToDafny.GrantTokenList(nativeValue.grantTokens());
    KMSConfiguration kmsConfiguration;
    kmsConfiguration = ToDafny.KMSConfiguration(nativeValue.kmsConfiguration());
    return new GetKeyStoreInfoOutput(
      keyStoreId,
      keyStoreName,
      logicalKeyStoreName,
      grantTokens,
      kmsConfiguration
    );
  }

  public static KeyStoreConfig KeyStoreConfig(
    software.amazon.cryptography.keystore.model.KeyStoreConfig nativeValue
  ) {
    DafnySequence<? extends Character> ddbTableName;
    ddbTableName =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.ddbTableName()
      );
    KMSConfiguration kmsConfiguration;
    kmsConfiguration = ToDafny.KMSConfiguration(nativeValue.kmsConfiguration());
    DafnySequence<? extends Character> logicalKeyStoreName;
    logicalKeyStoreName =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.logicalKeyStoreName()
      );
    Option<DafnySequence<? extends Character>> id;
    id =
      Objects.nonNull(nativeValue.id())
        ? Option.create_Some(
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.id()
          )
        )
        : Option.create_None();
    Option<
      DafnySequence<? extends DafnySequence<? extends Character>>
    > grantTokens;
    grantTokens =
      (Objects.nonNull(nativeValue.grantTokens()) &&
          nativeValue.grantTokens().size() > 0)
        ? Option.create_Some(ToDafny.GrantTokenList(nativeValue.grantTokens()))
        : Option.create_None();
    Option<IDynamoDBClient> ddbClient;
    ddbClient =
      Objects.nonNull(nativeValue.ddbClient())
        ? Option.create_Some(
          software.amazon.cryptography.services.dynamodb.internaldafny.ToDafny.DynamoDB_20120810(
            nativeValue.ddbClient()
          )
        )
        : Option.create_None();
    Option<IKMSClient> kmsClient;
    kmsClient =
      Objects.nonNull(nativeValue.kmsClient())
        ? Option.create_Some(
          software.amazon.cryptography.services.kms.internaldafny.ToDafny.TrentService(
            nativeValue.kmsClient()
          )
        )
        : Option.create_None();
    return new KeyStoreConfig(
      ddbTableName,
      kmsConfiguration,
      logicalKeyStoreName,
      id,
      grantTokens,
      ddbClient,
      kmsClient
    );
  }

  public static VersionKeyInput VersionKeyInput(
    software.amazon.cryptography.keystore.model.VersionKeyInput nativeValue
  ) {
    DafnySequence<? extends Character> branchKeyIdentifier;
    branchKeyIdentifier =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.branchKeyIdentifier()
      );
    return new VersionKeyInput(branchKeyIdentifier);
  }

  public static VersionKeyOutput VersionKeyOutput(
    software.amazon.cryptography.keystore.model.VersionKeyOutput nativeValue
  ) {
    return new VersionKeyOutput();
  }

  public static Error Error(KeyStoreException nativeValue) {
    DafnySequence<? extends Character> message;
    message =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.message()
      );
    return new Error_KeyStoreException(message);
  }

  public static KMSConfiguration KMSConfiguration(
    software.amazon.cryptography.keystore.model.KMSConfiguration nativeValue
  ) {
    if (Objects.nonNull(nativeValue.kmsKeyArn())) {
      return KMSConfiguration.create(
        software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
          nativeValue.kmsKeyArn()
        )
      );
    }
    throw new IllegalArgumentException(
      "Cannot convert " +
      nativeValue +
      " to software.amazon.cryptography.keystore.internaldafny.types.KMSConfiguration."
    );
  }

  public static DafnySequence<
    ? extends DafnySequence<? extends Character>
  > GrantTokenList(List<String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Byte>,
    ? extends DafnySequence<? extends Byte>
  > EncryptionContext(Map<String, String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Character>,
    ? extends DafnySequence<? extends Byte>
  > HmacKeyMap(Map<String, ByteBuffer> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::ByteSequence
    );
  }

  public static IKeyStoreClient KeyStore(KeyStore nativeValue) {
    return nativeValue.impl();
  }
}
