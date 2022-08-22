package software.amazon.polymorph.smithyjava.generator.awssdk;

public class ToDafnyConstants {
    static String MESSAGE_DECLARATION_REQUIRED =
            "dafny.DafnySequence<? extends java.lang.Character> message";
    static String MESSAGE_DECLARATION_OPTIONAL =
            "Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Character>> message";
    static String MESSAGE_ASSIGNMENT_REQUIRED =
            "message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage())";
    static String IDENTITY_NORMAL_REFERENCE = "";
    static String TO_DAFNY_BLOB_CONVERSION = "software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence";
    static String TO_DAFNY_STRING_CONVERSION = "software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence";
    static String MESSAGE_ASSIGNMENT_OPTIONAL = """
                    message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                    Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                    : Wrappers_Compile.Option.create_None()""";
    static String MESSAGE_ASSIGNMENT_OPTIONAL_SPACED = """
                    message = java.util.Objects.nonNull(nativeValue.getMessage()) ?
                          Wrappers_Compile.Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.getMessage()))
                          : Wrappers_Compile.Option.create_None()""";
    static String RETURN_DO_SOMETHING_REQUIRED = "return new Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest(message)";
    static String DO_SOMETHING_REQUEST = """
            public static Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest DoSomethingRequest(
                com.amazonaws.services.kms.model.DoSomethingRequest nativeValue) {
              %s;
              %s;
              %s;
            }
            """.formatted(MESSAGE_DECLARATION_REQUIRED, MESSAGE_ASSIGNMENT_REQUIRED, RETURN_DO_SOMETHING_REQUIRED);
    static String RETURN_DO_SOMETHING_OPTIONAL = "return new Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse(message)";
    static String DO_SOMETHING_RESPONSE = """
            public static Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse DoSomethingResponse(
                com.amazonaws.services.kms.model.DoSomethingResult nativeValue) {
              %s;
              %s;
              %s;
            }
            """.formatted(MESSAGE_DECLARATION_OPTIONAL, MESSAGE_ASSIGNMENT_OPTIONAL_SPACED, RETURN_DO_SOMETHING_OPTIONAL);
}
