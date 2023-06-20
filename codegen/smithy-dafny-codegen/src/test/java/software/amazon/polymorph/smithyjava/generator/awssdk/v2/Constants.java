// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

public class Constants {
    static String DoSomethingOperation = """
              @Override
              public Result<DoSomethingResponse, Error> DoSomething(DoSomethingRequest input) {
                software.amazon.awssdk.services.kms.model.DoSomethingRequest converted = ToNative.DoSomethingRequest(input);
                try {
                  software.amazon.awssdk.services.kms.model.DoSomethingResponse result = _impl.doSomething(converted);
                  DoSomethingResponse dafnyResponse = ToDafny.DoSomethingResponse(result);
                  return Result.create_Success(dafnyResponse);
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (KmsException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String DoVoidOperation = """
              @Override
              public Result<Tuple0, Error> DoVoid(DoVoidRequest input) {
                software.amazon.awssdk.services.kms.model.DoVoidRequest converted = ToNative.DoVoidRequest(input);
                try {
                  _impl.doVoid(converted);
                  return Result.create_Success(Tuple0.create());
                } catch (DependencyTimeoutException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                } catch (KmsException ex) {
                  return Result.create_Failure(ToDafny.Error(ex));
                }
              }
            """;

    static String MockKmsShim = """
            package software.amazon.cryptography.services.kms.internaldafny;
            
            import Wrappers_Compile.Result;
            import dafny.Tuple0;
            import java.lang.Override;
            import java.lang.String;
            import software.amazon.awssdk.services.kms.KmsClient;
            import software.amazon.awssdk.services.kms.model.DependencyTimeoutException;
            import software.amazon.awssdk.services.kms.model.KmsException;            
            import software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingRequest;
            import software.amazon.cryptography.services.kms.internaldafny.types.DoSomethingResponse;
            import software.amazon.cryptography.services.kms.internaldafny.types.DoVoidRequest;
            import software.amazon.cryptography.services.kms.internaldafny.types.Error;
            import software.amazon.cryptography.services.kms.internaldafny.types.IKeyManagementServiceClient;
            
            public class Shim implements IKeyManagementServiceClient {
              private final KmsClient _impl;
              
              private final String region;
              
              public Shim(final KmsClient impl, final String region) {
                this._impl = impl;
                this.region = region;
              }
              
              public KmsClient impl() {
                return this._impl;
              }
              
              public String region() {
                return this.region;
              }
              
              %s
              %s
            }
            """.formatted(DoSomethingOperation, DoVoidOperation);

}
