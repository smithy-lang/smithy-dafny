// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static software.amazon.polymorph.smithyjava.generator.ToDafnyConstants.MEMBER_ASSIGNMENT_OPTIONAL;
import static software.amazon.polymorph.smithyjava.generator.ToDafnyConstants.MEMBER_DECLARATION_OPTIONAL;

public class ToDafnyAwsV2Constants {

  protected static String DO_SOMETHING_RESPONSE =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingResponse DoSomethingResponse(
        software.amazon.awssdk.services.kms.model.DoSomethingResponse nativeValue) {
      %s;
      %s;
      return new software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingResponse(message);
    }
    """.formatted(MEMBER_DECLARATION_OPTIONAL, MEMBER_ASSIGNMENT_OPTIONAL);

  protected static String KEY_USAGE_TYPE =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType KeyUsageType(
        software.amazon.awssdk.services.kms.model.KeyUsageType nativeValue
    ) {
      switch (nativeValue) {
        case SIGN_VERIFY: {
          return software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.create_SIGN__VERIFY();
        }
        case ENCRYPT_DECRYPT: {
          return software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.create_ENCRYPT__DECRYPT();
        }
        default: {
          throw new java.lang.RuntimeException("Cannot convert " + nativeValue + " to software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.");
        }
      }
    }
    """;

  protected static String KEY_USAGE_TYPE_STRING =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType KeyUsageType(
        java.lang.String nativeValue
    ) {
      return KeyUsageType(software.amazon.awssdk.services.kms.model.KeyUsageType.fromValue(nativeValue));
    }""";

  protected static String GENERATE_CONVERT_LIST =
    """
    public static dafny.DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType> KeyUsageTypes (
        java.util.List<software.amazon.awssdk.services.kms.model.KeyUsageType> nativeValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
          nativeValue,
          software.amazon.cryptography.services.kms.internaldafny.ToDafny::KeyUsageType,
          software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType._typeDescriptor()
      );
    }
    """;
  protected static String GENERATE_CONVERT_LIST_STRUCTURES =
    """
    public static dafny.DafnySequence<? extends software.amazon.cryptography.services.other.internaldafny.types.OtherNamespace> OtherNamespaces (
        java.util.List<software.amazon.awssdk.services.other.model.OtherNamespace> nativeValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
          nativeValue,
          software.amazon.cryptography.services.other.internaldafny.ToDafny::OtherNamespace,
          software.amazon.cryptography.services.other.internaldafny.types.OtherNamespace._typeDescriptor()
      );
    }
    """;
  protected static String GENERATE_CONVERT_MAP_STRING =
    """
    public static dafny.DafnyMap<
            ? extends dafny.DafnySequence<? extends java.lang.Character>,
            ? extends dafny.DafnySequence<? extends java.lang.Character>>
    EncryptionContextType(
        java.util.Map<java.lang.String, java.lang.String> nativeValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
          nativeValue,
          software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
          software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
      );
    }
    """;
  protected static String GENERATE_CONVERT_SET_STRING =
    """
    public static dafny.DafnySet<
           ? extends dafny.DafnySequence<? extends java.lang.Character>>
    Names(
        java.util.Set<java.lang.String> nativeValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSet(
          nativeValue,
          software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
      );
    }
    """;

  public static String SIMPLE_STRUCTURE =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.Simple Simple(
        software.amazon.awssdk.services.kms.model.Simple nativeValue) {
      return new software.amazon.cryptography.services.kms.internaldafny.types.Simple();
    }
    """;

  protected static String GENERATE_CONVERT_OPAQUE_ERROR =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.Error Error(
            java.lang.Exception nativeValue
    ) {
      // While this is logically identical to the other Opaque Error case,
      // it is semantically distinct.
      // An un-modeled Service Error is different from a Java Heap Exhaustion error.
      // In the future, Smithy-Dafny MAY allow for this distinction.
      // Which would allow Dafny developers to treat the two differently.
      return software.amazon.cryptography.services.kms.internaldafny.types.Error.create_Opaque(nativeValue);
    }
    """;

  protected static String GENERATE_CONVERT_OPAQUE_ERROR_WITH_TYPE_DESCRIPTORS =
    """
    public static software.amazon.cryptography.services.kms.internaldafny.types.Error Error(
      java.lang.Exception nativeValue
    ) {
      // While this is logically identical to the other Opaque Error case,
      // it is semantically distinct.
      // An un-modeled Service Error is different from a Java Heap Exhaustion error.
      // In the future, Smithy-Dafny MAY allow for this distinction.
      // Which would allow Dafny developers to treat the two differently.
      return software.amazon.cryptography.services.kms.internaldafny.types.Error.create_Opaque(nativeValue);
    }
    """;

  protected static final String KMS_A_STRING_OPERATION_JAVA_FILE =
    """
    package software.amazon.cryptography.services.kms.internaldafny;

    import software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingResponse;
    import software.amazon.cryptography.services.kms.internaldafny.types.Error;
    import software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException;
    import software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque;
    import Wrappers_Compile.Option;
    import dafny.DafnySequence;
    import java.lang.Character;
    import java.util.Objects;
    import software.amazon.awssdk.services.kms.model.KmsException;
    import software.amazon.awssdk.services.kms.model.DependencyTimeoutException;

    public class ToDafny {
      public static DoSomethingResponse DoSomethingResponse(DoSomethingResponse nativeValue) {
        Option<DafnySequence<? extends Character>> message;
        message = Objects.nonNull(nativeValue.getMessage()) ?
            Option.create_Some(software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
            : Option.create_None();
        return new DoSomethingResponse(message);
      }

      public static Error Error(DependencyTimeoutException nativeValue) {
        Option<DafnySequence<? extends Character>> message;
        message = Objects.nonNull(nativeValue.getMessage()) ?
            Option.create_Some(software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
            : Option.create_None();
        return new Error_DependencyTimeoutException(message);
      }

      public static Error Error(KmsException nativeValue) {
        Option<DafnySequence<? extends Character>> message;
        message = Objects.nonNull(nativeValue.getMessage()) ?
            Option.create_Some(software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
            : Option.create_None();
        return new Error_Opaque(message);
      }
    }""";
}
