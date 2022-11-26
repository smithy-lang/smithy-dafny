package software.amazon.polymorph.smithyjava.generator.awssdk;

public class ToNativeConstants {
    static String STRING_CONVERSION = "software.amazon.dafny.conversion.ToNative.Simple.String";
    static String KEY_USAGE_TYPE_CONVERSION = "Dafny.Com.Amazonaws.Kms.ToNative.KeyUsageType";
    static String OTHER_NAMESPACE_CONVERSION = "Dafny.Com.Amazonaws.Other.ToNative.OtherNamespace";
    static String INIT_TEMP_ARRAY = "com.amazonaws.services.kms.model.KeyUsageType[] listEnum_temp = new com.amazonaws.services.kms.model.KeyUsageType[dafnyValue._listEnum.length()]";
    static String SET_WITH_CONVERSION_CALL = "converted.withCiphertext(software.amazon.dafny.conversion.ToNative.Simple.ByteBuffer(dafnyValue._ciphertext))";
    static String SET_WITH_CONVERSION_CALL_AND_TO_ARRAY = "converted.withListEnum(Dafny.Com.Amazonaws.Kms.ToNative.KeyUsageTypes(dafnyValue._listEnum).toArray(listEnum_temp))";
    static String KEY_USAGE_TYPE = """
              public static com.amazonaws.services.kms.model.KeyUsageType KeyUsageType(
                      Dafny.Com.Amazonaws.Kms.Types.KeyUsageType dafnyValue
              ) {
                if (dafnyValue.is_SIGN__VERIFY()) {
                  return com.amazonaws.services.kms.model.KeyUsageType.SIGN_VERIFY;
                }
                if (dafnyValue.is_ENCRYPT__DECRYPT()) {
                  return com.amazonaws.services.kms.model.KeyUsageType.ENCRYPT_DECRYPT;
                }
                return com.amazonaws.services.kms.model.KeyUsageType.fromValue(dafnyValue.toString());
              }""";
    static String GENERATE_CONVERT_LIST = """
            public static java.util.List<com.amazonaws.services.kms.model.KeyUsageType> KeyUsageTypes(
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
            public static com.amazonaws.services.kms.model.Simple Simple(
              Dafny.Com.Amazonaws.Kms.Types.Simple dafnyValue
            ) {
              return new com.amazonaws.services.kms.model.Simple();
            }
            """;
    static String A_OPTIONAL_STRUCTURE = """
            public static com.amazonaws.services.kms.model.AOptional AOptional(
              Dafny.Com.Amazonaws.Kms.Types.AOptional dafnyValue
            ) {
              com.amazonaws.services.kms.model.AOptional converted = new com.amazonaws.services.kms.model.AOptional();
              if (dafnyValue._message.is_Some()) {
                converted.withMessage(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue._message.dtor_value()));
              }
              return converted;
            }
            """;
    static String REQUIRED_LIST_ENUM_STRUCTURE = """
            public static com.amazonaws.services.kms.model.RequiredListEnum RequiredListEnum(
              Dafny.Com.Amazonaws.Kms.Types.RequiredListEnum dafnyValue
            ) {
              com.amazonaws.services.kms.model.RequiredListEnum converted = new com.amazonaws.services.kms.model.RequiredListEnum();
              %s;
              %s;
              return converted;
            }
            """.formatted(INIT_TEMP_ARRAY, SET_WITH_CONVERSION_CALL_AND_TO_ARRAY);
    static String KMS_A_STRING_OPERATION_JAVA_FILE = """
            package Dafny.Com.Amazonaws.Kms;
            
            import com.amazonaws.services.kms.model.DoSomethingRequest;
            
            public class ToNative {
              public static DoSomethingRequest DoSomethingRequest(
                  Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest dafnyValue
              ) {
                DoSomethingRequest converted = new DoSomethingRequest();
                converted.withMessage(%s(dafnyValue._message));
                return converted;
              }
            }
            """.formatted(STRING_CONVERSION);
}
