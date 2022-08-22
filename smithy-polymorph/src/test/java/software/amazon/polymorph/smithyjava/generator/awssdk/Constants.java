package software.amazon.polymorph.smithyjava.generator.awssdk;

public class Constants {
    static String DoSomethingOperation = """
              @Override
              public Result<DoSomethingResponse, Error> DoSomething(DoSomethingRequest input) {
                com.amazonaws.services.kms.model.DoSomethingRequest converted = ToNative.DoSomethingRequest(input);
                try {
                  DoSomethingResult result = _impl.doSomething(converted);
                  DoSomethingResponse dafnyResponse = ToDafny.DoSomethingResponse(result);
                  return Result.create_Success(dafnyResponse);
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (AWSKMSException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String DoVoidOperation = """
              @Override
              public Result<Tuple0, Error> DoVoid(DoVoidRequest input) {
                com.amazonaws.services.kms.model.DoVoidRequest converted = ToNative.DoVoidRequest(input);
                try {
                  _impl.doVoid(converted);
                  return Result.create_Success(Tuple0.create());
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (AWSKMSException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String MockKmsShim = """
            package Dafny.Com.Amazonaws.Kms;
            
            import Dafny.Com.Amazonaws.Kms.Types.DoSomethingRequest;
            import Dafny.Com.Amazonaws.Kms.Types.DoSomethingResponse;
            import Dafny.Com.Amazonaws.Kms.Types.DoVoidRequest;
            import Dafny.Com.Amazonaws.Kms.Types.Error;
            import Dafny.Com.Amazonaws.Kms.Types.IKeyManagementServiceClient;
            
            import Wrappers_Compile.Result;
            
            import com.amazonaws.services.kms.AWSKMS;
            import com.amazonaws.services.kms.model.AWSKMSException;
            import com.amazonaws.services.kms.model.DependencyTimeoutException;
            import com.amazonaws.services.kms.model.DoSomethingResult;
            import dafny.Tuple0;
            
            import java.lang.Override;
            
            public class Shim implements IKeyManagementServiceClient {
              private final AWSKMS _impl;
              
              public Shim(AWSKMS impl) {
                _impl = impl;
              }
              
              %s
              %s
            }
            """.formatted(DoSomethingOperation, DoVoidOperation);

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

    static String TO_DAFNY_GRANT_TOKEN_LIST = """
            static public DafnySequence<? extends DafnySequence<? extends Character>> GrantTokenList(
                        java.util.Collection<java.lang.String> nativeValue
                ) {
                    Function<String, DafnySequence<? extends Character>> converter = software.amazon.dafny.conversion.ToDafny::CharacterSequence;
                    Function<DafnySequence<? extends Character>, Boolean> memberCheck = __default::IsValid__GrantTokenType;
                    Function<DafnySequence<? extends DafnySequence<? extends Character>>, Boolean> sequenceCheck = __default::IsValid__GrantTokenList;
                    TypeDescriptor<DafnySequence<? extends Character>> typeDescriptor = GrantTokenType._typeDescriptor();
                    return GenericConverter(nativeValue, converter, memberCheck, "IsValid__GrantTokenType", sequenceCheck, "IsValid__GrantTokenList", typeDescriptor);
                }""";
}
