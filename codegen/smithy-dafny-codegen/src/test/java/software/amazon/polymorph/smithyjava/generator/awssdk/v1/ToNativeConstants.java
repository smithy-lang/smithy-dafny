// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v1;

public class ToNativeConstants {

  static String STRING_CONVERSION =
    "software.amazon.smithy.dafny.conversion.ToNative.Simple.String";
  static String KEY_USAGE_TYPE_CONVERSION =
    "software.amazon.cryptography.services.kms.internaldafny.ToNative.KeyUsageType";
  static String OTHER_NAMESPACE_CONVERSION =
    "Dafny.Com.Amazonaws.Other.ToNative.OtherNamespace";
  static String INIT_TEMP_ARRAY =
    "com.amazonaws.services.kms.model.KeyUsageType[] listEnum_temp = new com.amazonaws.services.kms.model.KeyUsageType[dafnyValue.dtor_listEnum().length()]";
  static String SET_WITH_CONVERSION_CALL =
    "converted.withCiphertext(software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue.dtor_ciphertext()))";
  static String SET_WITH_CONVERSION_CALL_AND_TO_ARRAY =
    "converted.withListEnum(software.amazon.cryptography.services.kms.internaldafny.ToNative.KeyUsageTypes(dafnyValue.dtor_listEnum()).toArray(listEnum_temp))";
  static String KEY_USAGE_TYPE =
    """
    public static com.amazonaws.services.kms.model.KeyUsageType KeyUsageType(
            software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType dafnyValue
    ) {
      if (dafnyValue.is_SIGN__VERIFY()) {
        return com.amazonaws.services.kms.model.KeyUsageType.SIGN_VERIFY;
      }
      if (dafnyValue.is_ENCRYPT__DECRYPT()) {
        return com.amazonaws.services.kms.model.KeyUsageType.ENCRYPT_DECRYPT;
      }
      return com.amazonaws.services.kms.model.KeyUsageType.fromValue(dafnyValue.toString());
    }""";
  static String GENERATE_CONVERT_LIST =
    """
    public static java.util.List<com.amazonaws.services.kms.model.KeyUsageType> KeyUsageTypes(
        dafny.DafnySequence<? extends software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType> dafnyValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
          dafnyValue,
          software.amazon.cryptography.services.kms.internaldafny.ToNative::KeyUsageType);
    }
    """;
  static String GENERATE_CONVERT_SET =
    """
    public static java.util.Set<java.lang.String> Names(
        dafny.DafnySet<? extends dafny.DafnySequence<? extends java.lang.Character>> dafnyValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToSet(
          dafnyValue,
          software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
    }
    """;
  static String GENERATE_CONVERT_MAP =
    """
    public static java.util.Map<java.lang.String, java.lang.String> EncryptionContextType(
        dafny.DafnyMap<
                ? extends dafny.DafnySequence<? extends java.lang.Character>,
                ? extends dafny.DafnySequence<? extends java.lang.Character>
        > dafnyValue
    ) {
      return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
          dafnyValue,
          software.amazon.smithy.dafny.conversion.ToNative.Simple::String,
          software.amazon.smithy.dafny.conversion.ToNative.Simple::String);
    }""";
  static String SIMPLE_STRUCTURE =
    """
    public static com.amazonaws.services.kms.model.Simple Simple(
      software.amazon.cryptography.services.kms.internaldafny.types.Simple dafnyValue
    ) {
      return new com.amazonaws.services.kms.model.Simple();
    }
    """;
  static String A_OPTIONAL_STRUCTURE =
    """
    public static com.amazonaws.services.kms.model.AOptional AOptional(
      software.amazon.cryptography.services.kms.internaldafny.types.AOptional dafnyValue
    ) {
      com.amazonaws.services.kms.model.AOptional converted = new com.amazonaws.services.kms.model.AOptional();
      if (dafnyValue.dtor_message().is_Some()) {
        converted.withMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
      }
      return converted;
    }
    """;
  static String REQUIRED_LIST_ENUM_STRUCTURE =
    """
    public static com.amazonaws.services.kms.model.RequiredListEnum RequiredListEnum(
      software.amazon.cryptography.services.kms.internaldafny.types.RequiredListEnum dafnyValue
    ) {
      com.amazonaws.services.kms.model.RequiredListEnum converted = new com.amazonaws.services.kms.model.RequiredListEnum();
      %s;
      %s;
      return converted;
    }
    """.formatted(INIT_TEMP_ARRAY, SET_WITH_CONVERSION_CALL_AND_TO_ARRAY);
  static String KMS_A_STRING_OPERATION_JAVA_FILE =
    """
    package software.amazon.cryptography.services.kms.internaldafny;

    import software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException;
    import software.amazon.cryptography.services.kms.internaldafny.types.IKeyManagementServiceClient;
    import com.amazonaws.services.kms.AWSKMS;
    import com.amazonaws.services.kms.model.DependencyTimeoutException;
    import com.amazonaws.services.kms.model.DoSomethingRequest;
    import com.amazonaws.services.kms.model.DoSomethingResponse;
    import com.amazonaws.services.kms.model.DoSomethingResult;

    public class ToNative {
      public static DoSomethingResponse DoSomethingResponse(DoSomethingResult nativeValue) {
        DoSomethingResponse.Builder nativeBuilder = DoSomethingResponse.builder();
        if (dafnyValue.dtor_message().is_Some()) {
          converted.withMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
        }
        return nativeBuilder.build();
      }

      public static DoSomethingRequest DoSomethingRequest(
          software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingRequest dafnyValue) {
        DoSomethingRequest converted = new DoSomethingRequest();
        converted.withMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
        return converted;
      }

      public static DependencyTimeoutException Error(Error_DependencyTimeoutException dafnyValue) {
        DependencyTimeoutException converted = new DependencyTimeoutException();
        if (dafnyValue.dtor_message().is_Some()) {
          converted.withMessage(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
        }
        return converted;
      }

      public static AWSKMS KeyManagementService(IKeyManagementServiceClient dafnyValue) {
        return ((Shim) dafnyValue).impl();
      }
    }
    """;
}
