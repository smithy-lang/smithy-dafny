package software.amazon.polymorph.smithyjava.generator.awssdk;

public class ToNativeConstants {
    static String STRING_CONVERSION = "software.amazon.dafny.conversion.ToNative.Simple.String";
    static String KEY_USAGE_TYPE_CONVERSION = "Dafny.Com.Amazonaws.Kms.ToNative.KeyUsageType";
    static String OTHER_NAMESPACE_CONVERSION = "Dafny.Com.Amazonaws.Other.ToNative.OtherNamespace";
    static String INIT_TEMP_ARRAY = "com.amazonaws.services.kms.model.KeyUsageType[] listEnum_temp = new com.amazonaws.services.kms.model.KeyUsageType[dafnyValue.ListEnum.length()]";
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
}
