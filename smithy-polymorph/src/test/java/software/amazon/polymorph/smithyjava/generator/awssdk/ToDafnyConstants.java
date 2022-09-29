package software.amazon.polymorph.smithyjava.generator.awssdk;

public class ToDafnyConstants {
    static String MEMBER_DECLARATION_REQUIRED =
            "dafny.DafnySequence<? extends java.lang.Character> name";
    static String MEMBER_DECLARATION_OPTIONAL =
            "Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Character>> message";
    static String MEMBER_ASSIGNMENT_REQUIRED =
            "name = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getName())";
    static String STRING_CONVERSION = "software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence";
    static String KEY_USAGE_TYPE_CONVERSION = "Dafny.Com.Amazonaws.Kms.ToDafny.KeyUsageType";
    static String OTHER_NAMESPACE_CONVERSION = "Dafny.Com.Amazonaws.Other.ToDafny.OtherNamespace";
    static String MEMBER_ASSIGNMENT_OPTIONAL = """
                    message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                          Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                          : Wrappers_Compile.Option.create_None()""";
    static String RETURN_A_OPTIONAL = "return new Dafny.Com.Amazonaws.Kms.Types.AOptional(message)";
    static String SIMPLE_STRUCTURE = """
            public static Dafny.Com.Amazonaws.Kms.Types.Simple Simple(
                com.amazonaws.services.kms.model.Simple nativeValue) {
              return new Dafny.Com.Amazonaws.Kms.Types.Simple();
            }
            """;
    static String A_OPTIONAL_STRUCTURE = """
            public static Dafny.Com.Amazonaws.Kms.Types.AOptional AOptional(
                com.amazonaws.services.kms.model.AOptional nativeValue) {
              %s;
              %s;
              %s;
            }
            """.formatted(MEMBER_DECLARATION_OPTIONAL, MEMBER_ASSIGNMENT_OPTIONAL, RETURN_A_OPTIONAL);
    static String DO_SOMETHING_RESPONSE = """
            public static Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse DoSomethingResponse(
                com.amazonaws.services.kms.model.DoSomethingResult nativeValue) {
              %s;
              %s;
              return new Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse(message);
            }
            """.formatted(MEMBER_DECLARATION_OPTIONAL, MEMBER_ASSIGNMENT_OPTIONAL);
    static String KEY_USAGE_TYPE = """
            public static Dafny.Com.Amazonaws.Kms.Types.KeyUsageType KeyUsageType(
                com.amazonaws.services.kms.model.KeyUsageType nativeValue
            ) {
              switch (nativeValue) {
                case SIGN_VERIFY: {
                  return Dafny.Com.Amazonaws.Kms.Types.KeyUsageType.create_SIGN__VERIFY();
                }
                case ENCRYPT_DECRYPT: {
                  return Dafny.Com.Amazonaws.Kms.Types.KeyUsageType.create_ENCRYPT__DECRYPT();
                }
                default: {
                  throw new java.lang.RuntimeException("Cannot convert " + nativeValue + " to Dafny.Com.Amazonaws.Kms.Types.KeyUsageType.");
                }
              }
            }
            """;
    static String KEY_USAGE_TYPE_STRING = """
            public static Dafny.Com.Amazonaws.Kms.Types.KeyUsageType KeyUsageType(
                java.lang.String nativeValue
            ) {
              return KeyUsageType(com.amazonaws.services.kms.model.KeyUsageType.fromValue(nativeValue));
            }""";
    static String GENERATE_CONVERT_LIST = """
            public static dafny.DafnySequence<? extends Dafny.Com.Amazonaws.Kms.Types.KeyUsageType> KeyUsageTypes (
                java.util.List<java.lang.String> nativeValue
            ) {
              return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
                  nativeValue,
                  Dafny.Com.Amazonaws.Kms.ToDafny::KeyUsageType,
                  Dafny.Com.Amazonaws.Kms.Types.KeyUsageType._typeDescriptor()
              );
            }
            """;
    static String GENERATE_CONVERT_LIST_STRUCTURES = """
            public static dafny.DafnySequence<? extends Dafny.Com.Amazonaws.Other.Types.OtherNamespace> OtherNamespaces (
                java.util.List<com.amazonaws.services.other.model.OtherNamespace> nativeValue
            ) {
              return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
                  nativeValue,
                  Dafny.Com.Amazonaws.Other.ToDafny::OtherNamespace,
                  Dafny.Com.Amazonaws.Other.Types.OtherNamespace._typeDescriptor()
              );
            }
            """;
    static String GENERATE_CONVERT_MAP_STRING = """
            public static dafny.DafnyMap<
                    ? extends dafny.DafnySequence<? extends java.lang.Character>,
                    ? extends dafny.DafnySequence<? extends java.lang.Character>>
            EncryptionContextType(
                java.util.Map<java.lang.String, java.lang.String> nativeValue
            ) {
              return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
                  nativeValue,
                  software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence,
                  software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence
              );
            }
            """;
    static String GENERATE_CONVERT_SET_STRING = """
            public static dafny.DafnySet<
                   ? extends dafny.DafnySequence<? extends java.lang.Character>>
            Names(
                java.util.Set<java.lang.String> nativeValue
            ) {
              return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSet(
                  nativeValue,
                  software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence
              );
            }
            """;
    static String GENERATE_CONVERT_ERROR = """
            public static Dafny.Com.Amazonaws.Kms.Types.Error Error(
                    com.amazonaws.services.kms.model.DependencyTimeoutException nativeValue
            ) {
              Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Character>> message;
              message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                    Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                  : Wrappers_Compile.Option.create_None();
              return new Dafny.Com.Amazonaws.Kms.Types.Error_DependencyTimeoutException(message);
            }
            """;
    static String GENERATE_CONVERT_OPAQUE_ERROR = """
            public static Dafny.Com.Amazonaws.Kms.Types.Error Error(
                    com.amazonaws.services.kms.model.AWSKMSException nativeValue
            ) {
              Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Character>> message;
              message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                    Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                  : Wrappers_Compile.Option.create_None();
              return new Dafny.Com.Amazonaws.Kms.Types.Error_Opaque(message);
            }
            """;
    public static final String KMS_A_STRING_OPERATION_JAVA_FILE = """
            package Dafny.Com.Amazonaws.Kms;
                        
            import Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse;
            import Dafny.Com.Amazonaws.Kms.Types.Error;
            import Dafny.Com.Amazonaws.Kms.Types.Error_DependencyTimeoutException;
            import Dafny.Com.Amazonaws.Kms.Types.Error_Opaque;
            import Wrappers_Compile.Option;
            import com.amazonaws.services.kms.model.AWSKMSException;
            import com.amazonaws.services.kms.model.DependencyTimeoutException;
            import com.amazonaws.services.kms.model.DoSomethingResult;
            import dafny.DafnySequence;
            import java.lang.Character;
            import java.util.Objects;
                        
            public class ToDafny {
              public static DoSomethingResponse DoSomethingResponse(DoSomethingResult nativeValue) {
                Option<DafnySequence<? extends Character>> message;
                message = Objects.nonNull(nativeValue.getMessage()) ?
                    Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                    : Option.create_None();
                return new DoSomethingResponse(message);
              }
                        
              public static Error Error(DependencyTimeoutException nativeValue) {
                Option<DafnySequence<? extends Character>> message;
                message = Objects.nonNull(nativeValue.getMessage()) ?
                    Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                    : Option.create_None();
                return new Error_DependencyTimeoutException(message);
              }
                        
              public static Error Error(AWSKMSException nativeValue) {
                Option<DafnySequence<? extends Character>> message;
                message = Objects.nonNull(nativeValue.getMessage()) ?
                    Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                    : Option.create_None();
                return new Error_Opaque(message);
              }
            }""";
}
