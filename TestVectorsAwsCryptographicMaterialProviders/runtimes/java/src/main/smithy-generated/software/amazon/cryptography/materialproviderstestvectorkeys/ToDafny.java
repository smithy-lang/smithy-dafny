// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys;

import Wrappers_Compile.Option;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.internaldafny.types.DiscoveryFilter;
import software.amazon.cryptography.materialproviders.internaldafny.types.PaddingScheme;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.CmmOperation;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error_KeyVectorException;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionOutput;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.HierarchyKeyring;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KMSInfo;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAware;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsMrkAwareDiscovery;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KmsRsaKeyring;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.MultiKeyring;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawAES;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RawRSA;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.RequiredEncryptionContextCMM;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionOutput;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.StaticKeyring;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorCmmInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.CollectionOfErrors;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.KeyVectorException;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.OpaqueError;
import software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec;

public class ToDafny {

  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof KeyVectorException) {
      return ToDafny.Error((KeyVectorException) nativeValue);
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

  public static GetKeyDescriptionInput GetKeyDescriptionInput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.GetKeyDescriptionInput nativeValue
  ) {
    DafnySequence<? extends Byte> json;
    json =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
        nativeValue.json()
      );
    return new GetKeyDescriptionInput(json);
  }

  public static GetKeyDescriptionOutput GetKeyDescriptionOutput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.GetKeyDescriptionOutput nativeValue
  ) {
    KeyDescription keyDescription;
    keyDescription = ToDafny.KeyDescription(nativeValue.keyDescription());
    return new GetKeyDescriptionOutput(keyDescription);
  }

  public static HierarchyKeyring HierarchyKeyring(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.HierarchyKeyring nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    return new HierarchyKeyring(keyId);
  }

  public static KeyVectorsConfig KeyVectorsConfig(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KeyVectorsConfig nativeValue
  ) {
    DafnySequence<? extends Character> keyManifestPath;
    keyManifestPath =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyManifestPath()
      );
    return new KeyVectorsConfig(keyManifestPath);
  }

  public static KMSInfo KMSInfo(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KMSInfo nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    return new KMSInfo(keyId);
  }

  public static KmsMrkAware KmsMrkAware(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KmsMrkAware nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    return new KmsMrkAware(keyId);
  }

  public static KmsMrkAwareDiscovery KmsMrkAwareDiscovery(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KmsMrkAwareDiscovery nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    DafnySequence<? extends Character> defaultMrkRegion;
    defaultMrkRegion =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.defaultMrkRegion()
      );
    Option<DiscoveryFilter> awsKmsDiscoveryFilter;
    awsKmsDiscoveryFilter =
      Objects.nonNull(nativeValue.awsKmsDiscoveryFilter())
        ? Option.create_Some(
          software.amazon.cryptography.materialproviders.ToDafny.DiscoveryFilter(
            nativeValue.awsKmsDiscoveryFilter()
          )
        )
        : Option.create_None();
    return new KmsMrkAwareDiscovery(
      keyId,
      defaultMrkRegion,
      awsKmsDiscoveryFilter
    );
  }

  public static KmsRsaKeyring KmsRsaKeyring(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KmsRsaKeyring nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    EncryptionAlgorithmSpec encryptionAlgorithm;
    encryptionAlgorithm =
      software.amazon.cryptography.services.kms.internaldafny.ToDafny.EncryptionAlgorithmSpec(
        nativeValue.encryptionAlgorithm()
      );
    return new KmsRsaKeyring(keyId, encryptionAlgorithm);
  }

  public static MultiKeyring MultiKeyring(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.MultiKeyring nativeValue
  ) {
    Option<KeyDescription> generator;
    generator =
      Objects.nonNull(nativeValue.generator())
        ? Option.create_Some(ToDafny.KeyDescription(nativeValue.generator()))
        : Option.create_None();
    DafnySequence<? extends KeyDescription> childKeyrings;
    childKeyrings = ToDafny.KeyDescriptionList(nativeValue.childKeyrings());
    return new MultiKeyring(generator, childKeyrings);
  }

  public static RawAES RawAES(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.RawAES nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    DafnySequence<? extends Character> providerId;
    providerId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.providerId()
      );
    return new RawAES(keyId, providerId);
  }

  public static RawRSA RawRSA(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.RawRSA nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    DafnySequence<? extends Character> providerId;
    providerId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.providerId()
      );
    PaddingScheme padding;
    padding =
      software.amazon.cryptography.materialproviders.ToDafny.PaddingScheme(
        nativeValue.padding()
      );
    return new RawRSA(keyId, providerId, padding);
  }

  public static RequiredEncryptionContextCMM RequiredEncryptionContextCMM(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.RequiredEncryptionContextCMM nativeValue
  ) {
    KeyDescription underlying;
    underlying = ToDafny.KeyDescription(nativeValue.underlying());
    DafnySequence<
      ? extends DafnySequence<? extends Byte>
    > requiredEncryptionContextKeys;
    requiredEncryptionContextKeys =
      software.amazon.cryptography.materialproviders.ToDafny.EncryptionContextKeys(
        nativeValue.requiredEncryptionContextKeys()
      );
    return new RequiredEncryptionContextCMM(
      underlying,
      requiredEncryptionContextKeys
    );
  }

  public static SerializeKeyDescriptionInput SerializeKeyDescriptionInput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.SerializeKeyDescriptionInput nativeValue
  ) {
    KeyDescription keyDescription;
    keyDescription = ToDafny.KeyDescription(nativeValue.keyDescription());
    return new SerializeKeyDescriptionInput(keyDescription);
  }

  public static SerializeKeyDescriptionOutput SerializeKeyDescriptionOutput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.SerializeKeyDescriptionOutput nativeValue
  ) {
    DafnySequence<? extends Byte> json;
    json =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
        nativeValue.json()
      );
    return new SerializeKeyDescriptionOutput(json);
  }

  public static StaticKeyring StaticKeyring(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.StaticKeyring nativeValue
  ) {
    DafnySequence<? extends Character> keyId;
    keyId =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.keyId()
      );
    return new StaticKeyring(keyId);
  }

  public static TestVectorCmmInput TestVectorCmmInput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.TestVectorCmmInput nativeValue
  ) {
    KeyDescription keyDescription;
    keyDescription = ToDafny.KeyDescription(nativeValue.keyDescription());
    CmmOperation forOperation;
    forOperation = ToDafny.CmmOperation(nativeValue.forOperation());
    return new TestVectorCmmInput(keyDescription, forOperation);
  }

  public static TestVectorKeyringInput TestVectorKeyringInput(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.TestVectorKeyringInput nativeValue
  ) {
    KeyDescription keyDescription;
    keyDescription = ToDafny.KeyDescription(nativeValue.keyDescription());
    return new TestVectorKeyringInput(keyDescription);
  }

  public static Error Error(KeyVectorException nativeValue) {
    DafnySequence<? extends Character> message;
    message =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.message()
      );
    return new Error_KeyVectorException(message);
  }

  public static CmmOperation CmmOperation(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.CmmOperation nativeValue
  ) {
    switch (nativeValue) {
      case ENCRYPT:
        {
          return CmmOperation.create_ENCRYPT();
        }
      case DECRYPT:
        {
          return CmmOperation.create_DECRYPT();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.CmmOperation."
          );
        }
    }
  }

  public static KeyDescription KeyDescription(
    software.amazon.cryptography.materialproviderstestvectorkeys.model.KeyDescription nativeValue
  ) {
    if (Objects.nonNull(nativeValue.Kms())) {
      return KeyDescription.create_Kms(ToDafny.KMSInfo(nativeValue.Kms()));
    }
    if (Objects.nonNull(nativeValue.KmsMrk())) {
      return KeyDescription.create_KmsMrk(
        ToDafny.KmsMrkAware(nativeValue.KmsMrk())
      );
    }
    if (Objects.nonNull(nativeValue.KmsMrkDiscovery())) {
      return KeyDescription.create_KmsMrkDiscovery(
        ToDafny.KmsMrkAwareDiscovery(nativeValue.KmsMrkDiscovery())
      );
    }
    if (Objects.nonNull(nativeValue.RSA())) {
      return KeyDescription.create_RSA(ToDafny.RawRSA(nativeValue.RSA()));
    }
    if (Objects.nonNull(nativeValue.AES())) {
      return KeyDescription.create_AES(ToDafny.RawAES(nativeValue.AES()));
    }
    if (Objects.nonNull(nativeValue.Static())) {
      return KeyDescription.create_Static(
        ToDafny.StaticKeyring(nativeValue.Static())
      );
    }
    if (Objects.nonNull(nativeValue.KmsRsa())) {
      return KeyDescription.create_KmsRsa(
        ToDafny.KmsRsaKeyring(nativeValue.KmsRsa())
      );
    }
    if (Objects.nonNull(nativeValue.Hierarchy())) {
      return KeyDescription.create_Hierarchy(
        ToDafny.HierarchyKeyring(nativeValue.Hierarchy())
      );
    }
    if (Objects.nonNull(nativeValue.Multi())) {
      return KeyDescription.create_Multi(
        ToDafny.MultiKeyring(nativeValue.Multi())
      );
    }
    if (Objects.nonNull(nativeValue.RequiredEncryptionContext())) {
      return KeyDescription.create_RequiredEncryptionContext(
        ToDafny.RequiredEncryptionContextCMM(
          nativeValue.RequiredEncryptionContext()
        )
      );
    }
    throw new IllegalArgumentException(
      "Cannot convert " +
      nativeValue +
      " to software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyDescription."
    );
  }

  public static DafnySequence<? extends KeyDescription> KeyDescriptionList(
    List<
      software.amazon.cryptography.materialproviderstestvectorkeys.model.KeyDescription
    > nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.materialproviderstestvectorkeys.ToDafny::KeyDescription,
      KeyDescription._typeDescriptor()
    );
  }

  public static IKeyVectorsClient KeyVectors(KeyVectors nativeValue) {
    return nativeValue.impl();
  }
}
