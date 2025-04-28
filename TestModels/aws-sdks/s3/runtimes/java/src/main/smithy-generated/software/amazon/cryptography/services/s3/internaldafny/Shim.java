// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.s3.internaldafny;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.Producers_Compile.Producer;
import Streams.ProviderAsInputStream;
import Wrappers_Compile.Result;
import java.lang.Override;
import java.lang.String;

import software.amazon.awssdk.core.ResponseInputStream;
import software.amazon.awssdk.core.sync.RequestBody;
import software.amazon.awssdk.http.ContentStreamProvider;
import software.amazon.awssdk.services.s3.S3Client;
import software.amazon.awssdk.services.s3.model.DeleteObjectResponse;
import software.amazon.awssdk.services.s3.model.DeleteObjectsResponse;
import software.amazon.awssdk.services.s3.model.GetObjectResponse;
import software.amazon.awssdk.services.s3.model.InvalidObjectStateException;
import software.amazon.awssdk.services.s3.model.ListObjectsV2Response;
import software.amazon.awssdk.services.s3.model.NoSuchBucketException;
import software.amazon.awssdk.services.s3.model.NoSuchKeyException;
import software.amazon.awssdk.services.s3.model.PutObjectResponse;
import software.amazon.awssdk.services.s3.model.S3Exception;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.Error;
import software.amazon.cryptography.services.s3.internaldafny.types.GetObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.GetObjectRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.IS3Client;
import software.amazon.cryptography.services.s3.internaldafny.types.ListObjectsV2Output;
import software.amazon.cryptography.services.s3.internaldafny.types.ListObjectsV2Request;
import software.amazon.cryptography.services.s3.internaldafny.types.PutObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.PutObjectRequest;

public class Shim implements IS3Client {

  private final S3Client _impl;

  private final String region;

  public Shim(final S3Client impl, final String region) {
    this._impl = impl;
    this.region = region;
  }

  public S3Client impl() {
    return this._impl;
  }

  public String region() {
    return this.region;
  }

  @Override
  public Result<DeleteObjectOutput, Error> DeleteObject(
    DeleteObjectRequest input
  ) {
    software.amazon.awssdk.services.s3.model.DeleteObjectRequest converted =
      ToNative.DeleteObjectRequest(input);
    try {
      DeleteObjectResponse result = _impl.deleteObject(converted);
      DeleteObjectOutput dafnyResponse = ToDafny.DeleteObjectOutput(result);
      return Result.create_Success(
        DeleteObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyResponse
      );
    } catch (S3Exception ex) {
      return Result.create_Failure(
        DeleteObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (Exception ex) {
      return Result.create_Failure(
        DeleteObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }

  @Override
  public Result<DeleteObjectsOutput, Error> DeleteObjects(
    DeleteObjectsRequest input
  ) {
    software.amazon.awssdk.services.s3.model.DeleteObjectsRequest converted =
      ToNative.DeleteObjectsRequest(input);
    try {
      DeleteObjectsResponse result = _impl.deleteObjects(converted);
      DeleteObjectsOutput dafnyResponse = ToDafny.DeleteObjectsOutput(result);
      return Result.create_Success(
        DeleteObjectsOutput._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyResponse
      );
    } catch (S3Exception ex) {
      return Result.create_Failure(
        DeleteObjectsOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (Exception ex) {
      return Result.create_Failure(
        DeleteObjectsOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }

  @Override
  public Result<GetObjectOutput, Error> GetObject(GetObjectRequest input) {
    software.amazon.awssdk.services.s3.model.GetObjectRequest converted =
      ToNative.GetObjectRequest(input);
    try {
      ResponseInputStream<GetObjectResponse> result = _impl.getObject(converted);
      GetObjectOutput dafnyResponse = ToDafny.GetObjectOutput(result);
      return Result.create_Success(
        GetObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyResponse
      );
    } catch (InvalidObjectStateException ex) {
      return Result.create_Failure(
        GetObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (NoSuchKeyException ex) {
      return Result.create_Failure(
        GetObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (S3Exception ex) {
      return Result.create_Failure(
        GetObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (Exception ex) {
      return Result.create_Failure(
        GetObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }

  @Override
  public Result<ListObjectsV2Output, Error> ListObjectsV2(
    ListObjectsV2Request input
  ) {
    software.amazon.awssdk.services.s3.model.ListObjectsV2Request converted =
      ToNative.ListObjectsV2Request(input);
    try {
      ListObjectsV2Response result = _impl.listObjectsV2(converted);
      ListObjectsV2Output dafnyResponse = ToDafny.ListObjectsV2Output(result);
      return Result.create_Success(
        ListObjectsV2Output._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyResponse
      );
    } catch (NoSuchBucketException ex) {
      return Result.create_Failure(
        ListObjectsV2Output._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (S3Exception ex) {
      return Result.create_Failure(
        ListObjectsV2Output._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (Exception ex) {
      return Result.create_Failure(
        ListObjectsV2Output._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }

  @Override
  public Result<PutObjectOutput, Error> PutObject(PutObjectRequest input) {
    software.amazon.awssdk.services.s3.model.PutObjectRequest converted =
      ToNative.PutObjectRequest(input);
    DataStream<Byte, Error> dataStream = input._Body.dtor_value();
    ContentStreamProvider provider = () -> {
      Producer reader = dataStream.Reader();
      return new ProviderAsInputStream(reader);
    };
    RequestBody body = dataStream.ContentLength().is_Some()
            ? RequestBody.fromContentProvider(provider, dataStream.ContentLength().dtor_value().longValueExact(), "application/octet-stream")
            : RequestBody.fromContentProvider(provider, "application/octet-stream");
    try {
      PutObjectResponse result = _impl.putObject(converted, body);
      PutObjectOutput dafnyResponse = ToDafny.PutObjectOutput(result);
      return Result.create_Success(
        PutObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyResponse
      );
    } catch (S3Exception ex) {
      return Result.create_Failure(
        PutObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    } catch (Exception ex) {
      return Result.create_Failure(
        PutObjectOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }
}
