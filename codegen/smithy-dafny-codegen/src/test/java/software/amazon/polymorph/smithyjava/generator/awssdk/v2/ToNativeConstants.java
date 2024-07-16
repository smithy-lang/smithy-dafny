// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

public class ToNativeConstants {

  static String STRING_CONVERSION =
    "software.amazon.smithy.dafny.conversion.ToNative.Simple.String";
  static String KEY_USAGE_TYPE_CONVERSION =
    "software.amazon.cryptography.services.kms.internaldafny.ToNative.KeyUsageType";
  static String OTHER_NAMESPACE_CONVERSION =
    "software.amazon.cryptography.services.other.internaldafny.ToNative.OtherNamespace";
  static String INIT_TEMP_ARRAY =
    "software.amazon.awssdk.services.kms.model.KeyUsageType[] listEnum_temp = new software.amazon.awssdk.services.kms.model.KeyUsageType[dafnyValue.dtor_listEnum().length()]";
  static String SET_WITH_CONVERSION_CALL =
    "builder.ciphertext(software.amazon.awssdk.core.SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ciphertext().toRawArray())))";
  static String SET_WITH_CONVERSION_CALL_AND_TO_ARRAY =
    "builder.listEnum(software.amazon.cryptography.services.kms.internaldafny.ToNative.KeyUsageTypes(dafnyValue.dtor_listEnum()).toArray(listEnum_temp))";
  static String KEY_USAGE_TYPE =
    """
    public static software.amazon.awssdk.services.kms.model.KeyUsageType KeyUsageType(
            software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType dafnyValue
    ) {
      if (dafnyValue.is_SIGN__VERIFY()) {
        return software.amazon.awssdk.services.kms.model.KeyUsageType.SIGN_VERIFY;
      }
      if (dafnyValue.is_ENCRYPT__DECRYPT()) {
        return software.amazon.awssdk.services.kms.model.KeyUsageType.ENCRYPT_DECRYPT;
      }
      return software.amazon.awssdk.services.kms.model.KeyUsageType.fromValue(dafnyValue.toString());
    }""";
  static String GENERATE_CONVERT_LIST =
    """
    public static java.util.List<software.amazon.awssdk.services.kms.model.KeyUsageType> KeyUsageTypes(
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
    public static software.amazon.awssdk.services.kms.model.Simple Simple(
      software.amazon.cryptography.services.kms.internaldafny.types.Simple dafnyValue
    ) {
      return software.amazon.awssdk.services.kms.model.Simple.builder().build();
    }
    """;
  static String A_OPTIONAL_STRUCTURE =
    """
    public static software.amazon.awssdk.services.kms.model.AOptional AOptional(
      software.amazon.cryptography.services.kms.internaldafny.types.AOptional dafnyValue
    ) {
      software.amazon.awssdk.services.kms.model.AOptional.Builder builder = software.amazon.awssdk.services.kms.model.AOptional.builder();
      if (dafnyValue.dtor_message().is_Some()) {
        builder.message(software.amazon.smithy.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
      }
      return builder.build();
    }
    """;
  static String REQUIRED_LIST_ENUM_STRUCTURE =
    """
    public static software.amazon.awssdk.services.kms.model.RequiredListEnum RequiredListEnum(
      software.amazon.cryptography.services.kms.internaldafny.types.RequiredListEnum dafnyValue
    ) {
      software.amazon.awssdk.services.kms.model.RequiredListEnum.Builder builder = software.amazon.awssdk.services.kms.model.RequiredListEnum.builder();
      %s;
      %s;
      return builder.build();
    }
    """.formatted(INIT_TEMP_ARRAY, SET_WITH_CONVERSION_CALL_AND_TO_ARRAY);
  static String KMS_A_STRING_OPERATION_JAVA_FILE =
    """
    package software.amazon.cryptography.services.kms.internaldafny;

     import java.lang.Exception;
     import java.lang.IllegalStateException;
     import java.lang.RuntimeException;
     import software.amazon.awssdk.services.kms.KmsClient;
     import software.amazon.awssdk.services.kms.model.DependencyTimeoutException;
     import software.amazon.awssdk.services.kms.model.DoSomethingRequest;
     import software.amazon.awssdk.services.kms.model.DoSomethingResponse;
     import software.amazon.awssdk.services.kms.model.KmsException;
     import software.amazon.cryptography.services.kms.internaldafny.types.Error_DependencyTimeoutException;
     import software.amazon.cryptography.services.kms.internaldafny.types.Error_Opaque;
     import software.amazon.cryptography.services.kms.internaldafny.types.IKeyManagementServiceClient;

     public class ToNative {
       public static DoSomethingRequest DoSomethingRequest(
           software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingRequest dafnyValue) {
         DoSomethingRequest.Builder builder = DoSomethingRequest.builder();
         builder.message(%s(dafnyValue.dtor_message()));
         return builder.build();
       }

       public static DoSomethingResponse DoSomethingResponse(
           software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingResponse dafnyValue) {
         DoSomethingResponse.Builder builder = DoSomethingResponse.builder();
         if (dafnyValue.dtor_message().is_Some()) {
           builder.message(%s(dafnyValue.dtor_message().dtor_value()));
         }
         return builder.build();
       }

       public static DependencyTimeoutException Error(Error_DependencyTimeoutException dafnyValue) {
         DependencyTimeoutException.Builder builder = DependencyTimeoutException.builder();
         if (dafnyValue.dtor_message().is_Some()) {
           builder.message(%s(dafnyValue.dtor_message().dtor_value()));
         }
         return builder.build();
       }

       public static KmsClient KeyManagementService(IKeyManagementServiceClient dafnyValue) {
           return ((Shim) dafnyValue).impl();
       }

       public static RuntimeException Error(Error_Opaque dafnyValue) {
         // While the first two cases are logically identical,
         // there is a semantic distinction.
         // An un-modeled Service Error is different from a Java Heap Exhaustion error.
         // In the future, Smithy-Dafny MAY allow for this distinction.
         // Which would allow Dafny developers to treat the two differently.
         if (dafnyValue.dtor_obj() instanceof KmsException) {
           return (KmsException) dafnyValue.dtor_obj();
         } else if (dafnyValue.dtor_obj() instanceof Exception) {
           return (RuntimeException) dafnyValue.dtor_obj();
         }
         return new IllegalStateException(String.format(%s, dafnyValue));
       }
     }
    """.formatted(
        STRING_CONVERSION,
        STRING_CONVERSION,
        STRING_CONVERSION,
        "\"Unknown error thrown while calling AWS. %s\""
      );
}
