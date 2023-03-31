package software.amazon.polymorph.smithyjava.generator;

public class ToDafnyConstants {
    public static String MEMBER_DECLARATION_REQUIRED =
            "dafny.DafnySequence<? extends java.lang.Character> name";
    public static String MEMBER_DECLARATION_OPTIONAL =
            "Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Character>> message";
    public static String MEMBER_ASSIGNMENT_REQUIRED =
            "name = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getName())";
    public static String STRING_CONVERSION = "software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence";
    public static String KEY_USAGE_TYPE_CONVERSION = "Dafny.Com.Amazonaws.Kms.ToDafny.KeyUsageType";
    public static String OTHER_NAMESPACE_CONVERSION = "Dafny.Com.Amazonaws.Other.ToDafny.OtherNamespace";
    public static String MEMBER_ASSIGNMENT_OPTIONAL = """
                    message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                          Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                          : Wrappers_Compile.Option.create_None()""";
    public static String RETURN_A_OPTIONAL = "return new Dafny.Com.Amazonaws.Kms.Types.AOptional(message)";
    public static String SIMPLE_STRUCTURE = """
            public static Dafny.Com.Amazonaws.Kms.Types.Simple Simple(
                com.amazonaws.services.kms.model.Simple nativeValue) {
              return new Dafny.Com.Amazonaws.Kms.Types.Simple();
            }
            """;
    public static String A_OPTIONAL_STRUCTURE = """
            public static Dafny.Com.Amazonaws.Kms.Types.AOptional AOptional(
                com.amazonaws.services.kms.model.AOptional nativeValue) {
              %s;
              %s;
              %s;
            }
            """.formatted(MEMBER_DECLARATION_OPTIONAL, MEMBER_ASSIGNMENT_OPTIONAL, RETURN_A_OPTIONAL);


    public static String GENERATE_CONVERT_ERROR = """
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


}
