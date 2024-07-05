// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;

public class Constants {

  static String DoSomethingOperation =
    """
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
        } catch (Exception ex) {
          return Result.create_Failure(ToDafny.Error(ex));
        }
      }
    """;

  static String DoSomethingOperationWithTypeDescriptors =
    """
      @Override
      public Result<DoSomethingResponse, Error> DoSomething(DoSomethingRequest input) {
        software.amazon.awssdk.services.kms.model.DoSomethingRequest converted = ToNative.DoSomethingRequest(input);
        try {
          software.amazon.awssdk.services.kms.model.DoSomethingResponse result = _impl.doSomething(converted);
          DoSomethingResponse dafnyResponse = ToDafny.DoSomethingResponse(result);
          return Result.create_Success(DoSomethingResponse._typeDescriptor(), Error._typeDescriptor(), dafnyResponse);
        } catch (DependencyTimeoutException ex) {
          return Result.create_Failure(DoSomethingResponse._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        } catch (KmsException ex) {
          return Result.create_Failure(DoSomethingResponse._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        } catch (Exception ex) {
          return Result.create_Failure(DoSomethingResponse._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        }
      }
    """;

  static String DoSomethingOperation(DafnyVersion dafnyVersion) {
    return Dafny.datatypeConstructorsNeedTypeDescriptors(dafnyVersion)
      ? DoSomethingOperationWithTypeDescriptors
      : DoSomethingOperation;
  }

  static String DoVoidOperation =
    """
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
        } catch (Exception ex) {
          return Result.create_Failure(ToDafny.Error(ex));
        }
      }
    """;

  static String DoVoidOperationWithTypeDescriptors =
    """
      @Override
      public Result<Tuple0, Error> DoVoid(DoVoidRequest input) {
        software.amazon.awssdk.services.kms.model.DoVoidRequest converted = ToNative.DoVoidRequest(input);
        try {
          _impl.doVoid(converted);
          return Result.create_Success(dafny.Tuple0._typeDescriptor(), Error._typeDescriptor(), Tuple0.create());
        } catch (DependencyTimeoutException ex) {
          return Result.create_Failure(dafny.Tuple0._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        } catch (KmsException ex) {
          return Result.create_Failure(dafny.Tuple0._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        } catch (Exception ex) {
          return Result.create_Failure(dafny.Tuple0._typeDescriptor(), Error._typeDescriptor(), ToDafny.Error(ex));
        }
      }
    """;

  static String DoVoidOperation(DafnyVersion dafnyVersion) {
    return Dafny.datatypeConstructorsNeedTypeDescriptors(dafnyVersion)
      ? DoVoidOperationWithTypeDescriptors
      : DoVoidOperation;
  }

  static String MockKmsShim =
    """
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

  static String MockKmsShimWithTypeDescriptors =
    """
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
    """.formatted(
        DoSomethingOperationWithTypeDescriptors,
        DoVoidOperationWithTypeDescriptors
      );

  static String MockKmsShim(DafnyVersion dafnyVersion) {
    return Dafny.datatypeConstructorsNeedTypeDescriptors(dafnyVersion)
      ? MockKmsShimWithTypeDescriptors
      : MockKmsShim;
  }
}
