package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

public class ToNativeConstants {
    static String STRING_CONVERSION = "software.amazon.dafny.conversion.ToNative.Simple.String";
    static String KEY_USAGE_TYPE_CONVERSION = "Dafny.Com.Amazonaws.Kms.ToNative.KeyUsageType";
    static String OTHER_NAMESPACE_CONVERSION = "com.amazonaws.other.ToNative.OtherNamespace";
    static String INIT_TEMP_ARRAY = "software.amazon.awssdk.services.kms.model.KeyUsageType[] listEnum_temp = new software.amazon.awssdk.services.kms.model.KeyUsageType[dafnyValue.dtor_listEnum().length()]";
    static String SET_WITH_CONVERSION_CALL = "builder.ciphertext(software.amazon.awssdk.core.SdkBytes.fromByteArray((byte[]) (dafnyValue.dtor_ciphertext().toRawArray())))";
    static String SET_WITH_CONVERSION_CALL_AND_TO_ARRAY = "builder.listEnum(Dafny.Com.Amazonaws.Kms.ToNative.KeyUsageTypes(dafnyValue.dtor_listEnum()).toArray(listEnum_temp))";
    static String KEY_USAGE_TYPE = """
              public static software.amazon.awssdk.services.kms.model.KeyUsageType KeyUsageType(
                      Dafny.Com.Amazonaws.Kms.Types.KeyUsageType dafnyValue
              ) {
                if (dafnyValue.is_SIGN__VERIFY()) {
                  return software.amazon.awssdk.services.kms.model.KeyUsageType.SIGN_VERIFY;
                }
                if (dafnyValue.is_ENCRYPT__DECRYPT()) {
                  return software.amazon.awssdk.services.kms.model.KeyUsageType.ENCRYPT_DECRYPT;
                }
                return software.amazon.awssdk.services.kms.model.KeyUsageType.fromValue(dafnyValue.toString());
              }""";
    static String GENERATE_CONVERT_LIST = """
            public static java.util.List<software.amazon.awssdk.services.kms.model.KeyUsageType> KeyUsageTypes(
                dafny.DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.KeyUsageType> dafnyValue
            ) {
              return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
                  dafnyValue,
                  Dafny.Com.Amazonaws.Kms.ToNative::KeyUsageType);
            }
            """;
    static String GENERATE_CONVERT_SET = """
            public static java.util.Set<java.lang.String> Names(
                dafny.DafnySet<? extends dafny.DafnySequence<? extends java.lang.Character>> dafnyValue
            ) {
              return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToSet(
                  dafnyValue,
                  software.amazon.dafny.conversion.ToNative.Simple::String);
            }
            """;
    static String GENERATE_CONVERT_MAP = """
            public static java.util.Map<java.lang.String, java.lang.String> EncryptionContextType(
                dafny.DafnyMap<
                        ? extends dafny.DafnySequence<? extends java.lang.Character>,
                        ? extends dafny.DafnySequence<? extends java.lang.Character>
                > dafnyValue
            ) {
              return software.amazon.dafny.conversion.ToNative.Aggregate.GenericToMap(
                  dafnyValue,
                  software.amazon.dafny.conversion.ToNative.Simple::String,
                  software.amazon.dafny.conversion.ToNative.Simple::String);
            }""";
    static String SIMPLE_STRUCTURE = """
            public static software.amazon.awssdk.services.kms.model.Simple Simple(
              Dafny.Com.Amazonaws.Kms.Types.Simple dafnyValue
            ) {
              return software.amazon.awssdk.services.kms.model.Simple.builder().build();
            }
            """;
    static String A_OPTIONAL_STRUCTURE = """
            public static software.amazon.awssdk.services.kms.model.AOptional AOptional(
              Dafny.Com.Amazonaws.Kms.Types.AOptional dafnyValue
            ) {
              software.amazon.awssdk.services.kms.model.AOptional.Builder builder = software.amazon.awssdk.services.kms.model.AOptional.builder();
              if (dafnyValue.dtor_message().is_Some()) {
                builder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message().dtor_value()));
              }
              return builder.build();
            }
            """;
    static String REQUIRED_LIST_ENUM_STRUCTURE = """
            public static software.amazon.awssdk.services.kms.model.RequiredListEnum RequiredListEnum(
              Dafny.Com.Amazonaws.Kms.Types.RequiredListEnum dafnyValue
            ) {
              software.amazon.awssdk.services.kms.model.RequiredListEnum.Builder builder = software.amazon.awssdk.services.kms.model.RequiredListEnum.builder();
              %s;
              %s;
              return builder.build();
            }
            """.formatted(INIT_TEMP_ARRAY, SET_WITH_CONVERSION_CALL_AND_TO_ARRAY);
    static String KMS_A_STRING_OPERATION_JAVA_FILE = """
            package Dafny.Com.Amazonaws.Kms;
            
            import software.amazon.awssdk.services.kms.model.DoSomethingRequest;
            
            public class ToNative {
              public static DoSomethingRequest DoSomethingRequest(
                  Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest dafnyValue
              ) {
                DoSomethingRequest.Builder builder = DoSomethingRequest.builder();
                builder.message(%s(dafnyValue.dtor_message()));
                return builder.build();
              }
            }
            """.formatted(STRING_CONVERSION);
}
