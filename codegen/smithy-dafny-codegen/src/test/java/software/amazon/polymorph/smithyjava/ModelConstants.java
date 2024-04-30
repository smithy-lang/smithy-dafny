// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

public class ModelConstants {

  public static String MOCK_KMS =
    """
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

  public static String KMS_A_STRING_OPERATION =
    """
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

  public static String KMS_KITCHEN =
    """
        namespace com.amazonaws.kms
        use com.amazonaws.other#OtherNamespace
        service KeyManagementService {}
        blob CiphertextType
        string TagKeyType
        @enum([
          { name: "SIGN_VERIFY", value: "SIGN_VERIFY" },
          { name: "ENCRYPT_DECRYPT", value: "ENCRYPT_DECRYPT" },
        ])
        string KeyUsageType
        list KeyUsageTypes { member: KeyUsageType }
        list OtherNamespaces { member: OtherNamespace }
        string OptionalString
        set Names { member: String }
        map EncryptionContextType { key: String, value: String }
        structure Kitchen {
          @required ciphertext: CiphertextType,
          @required name: TagKeyType,
          @required keyUsage: KeyUsageType,
          @required otherNamespace: OtherNamespace,
          message: OptionalString,
          @required listEnum: KeyUsageTypes
        }
        structure Simple {}
        structure AOptional { message: OptionalString }
        structure RequiredListEnum { @required listEnum: KeyUsageTypes }
        double NotSupported
    """;

  public static String OTHER_NAMESPACE =
    """
    namespace com.amazonaws.other
    structure OtherNamespace {}
    service OtherService {}
    """;

  public static String CRYPTOGRAPHY_A_STRING_OPERATION =
    """
        namespace aws.cryptography.test
        @aws.polymorph#localService(
          sdkId: "Test",
          config: TestConfig,
        )
        service Test {
          operations: [DoSomething],
          errors: [TestError]
        }
        structure TestConfig {}
        operation DoSomething {
            input: DoSomethingRequest,
            output: DoSomethingResponse,
            errors: [TestError]
        }
        @error("client")
        structure TestError {
          @required
          message: String
        }
        structure DoSomethingRequest {
            @required
            message: String
        }
        structure DoSomethingResponse { message: String }
        @range(min: 0, max: 10) integer ZeroToTenInteger
        structure TestRangeMinMaxInteger {
           zeroToTen: ZeroToTenInteger
        }
        @length(min:256, max:256) blob Aes256Key
        structure TestLengthMinMaxBlob {
          key: Aes256Key
        }
    """;
}
