package software.amazon.polymorph.smithyjava;

public class ModelConstants {
     public static String MOCK_KMS = """
                 namespace com.amazonaws.kms
                 service KeyManagementService { operations: [DoSomething, DoVoid] }
                 operation DoSomething {
                     input: DoSomethingRequest,
                     output: DoSomethingResponse,
                     errors: [DependencyTimeoutException]
                 }
                 operation DoVoid {
                     input: DoVoidRequest,
                     errors: [DependencyTimeoutException]
                 }
                 @error("server")
                 structure DependencyTimeoutException { message: String }
                 structure DoSomethingRequest {}
                 structure DoSomethingResponse {}
                 structure DoVoidRequest {}
             """;

     public static String KMS_A_STRING_OPERATION = """
                namespace com.amazonaws.kms
                service KeyManagementService { operations: [DoSomething] }
                operation DoSomething {
                    input: DoSomethingRequest,
                    output: DoSomethingResponse,
                    errors: [DependencyTimeoutException]
                }
                @error("server")
                structure DependencyTimeoutException { message: String }
                structure DoSomethingRequest {
                    @required
                    message: String
                }
                structure DoSomethingResponse { message: String }
            """;

     public static String KMS_CONSTRAINED_SIMPLE_SHAPES = """
                namespace com.amazonaws.kms
                service KeyManagementService
                @length(min: 1, max: 6144) blob CiphertextType
                @box boolean NullableBooleanType
                @length(min:1, max:128) string TagKeyType
                @box @range(min: 1, max: 1000) integer LimitType
            """;

    public static String KMS_SIMPLE_SHAPES = """
                namespace com.amazonaws.kms
                service KeyManagementService {}
                blob CiphertextType
                boolean BooleanType
                string TagKeyType
                timestamp DateType
                integer LimitType
                structure Kitchen {
                  @required ciphertext: CiphertextType,
                  @required isTrue: BooleanType,
                  @required name: TagKeyType,
                  @required creationDate: DateType,
                  @required limit: LimitType
                }
            """;
}
