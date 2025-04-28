// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.s3.internaldafny;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Streams.InputStreamAsDataStream;
import Streams.RequestBodyAsDataStream;
import Wrappers_Compile.Option;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Boolean;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Exception;
import java.lang.Integer;
import java.lang.Long;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import software.amazon.awssdk.core.ResponseInputStream;
import software.amazon.awssdk.core.sync.RequestBody;
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
import software.amazon.cryptography.services.s3.internaldafny.types.ChecksumAlgorithm;
import software.amazon.cryptography.services.s3.internaldafny.types.ChecksumMode;
import software.amazon.cryptography.services.s3.internaldafny.types.CommonPrefix;
import software.amazon.cryptography.services.s3.internaldafny.types.Delete;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.DeletedObject;
import software.amazon.cryptography.services.s3.internaldafny.types.EncodingType;
import software.amazon.cryptography.services.s3.internaldafny.types.Error;
import software.amazon.cryptography.services.s3.internaldafny.types.ErrorShape;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_InvalidObjectState;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_NoSuchBucket;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_NoSuchKey;
import software.amazon.cryptography.services.s3.internaldafny.types.GetObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.GetObjectRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.IS3Client;
import software.amazon.cryptography.services.s3.internaldafny.types.IntelligentTieringAccessTier;
import software.amazon.cryptography.services.s3.internaldafny.types.ListObjectsV2Output;
import software.amazon.cryptography.services.s3.internaldafny.types.ListObjectsV2Request;
import software.amazon.cryptography.services.s3.internaldafny.types.S3Object;
import software.amazon.cryptography.services.s3.internaldafny.types.ObjectCannedACL;
import software.amazon.cryptography.services.s3.internaldafny.types.ObjectIdentifier;
import software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockLegalHoldStatus;
import software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockMode;
import software.amazon.cryptography.services.s3.internaldafny.types.ObjectStorageClass;
import software.amazon.cryptography.services.s3.internaldafny.types.OptionalObjectAttributes;
import software.amazon.cryptography.services.s3.internaldafny.types.Owner;
import software.amazon.cryptography.services.s3.internaldafny.types.PutObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.PutObjectRequest;
import software.amazon.cryptography.services.s3.internaldafny.types.ReplicationStatus;
import software.amazon.cryptography.services.s3.internaldafny.types.RequestCharged;
import software.amazon.cryptography.services.s3.internaldafny.types.RequestPayer;
import software.amazon.cryptography.services.s3.internaldafny.types.RestoreStatus;
import software.amazon.cryptography.services.s3.internaldafny.types.S3Object;
import software.amazon.cryptography.services.s3.internaldafny.types.ServerSideEncryption;
import software.amazon.cryptography.services.s3.internaldafny.types.StorageClass;

public class ToDafny {

  public static DafnySequence<
    ? extends ChecksumAlgorithm
  > ChecksumAlgorithmList(
    List<software.amazon.awssdk.services.s3.model.ChecksumAlgorithm> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::ChecksumAlgorithm,
      ChecksumAlgorithm._typeDescriptor()
    );
  }

  public static CommonPrefix CommonPrefix(
    software.amazon.awssdk.services.s3.model.CommonPrefix nativeValue
  ) {
    Option<DafnySequence<? extends Character>> prefix;
    prefix =
      Objects.nonNull(nativeValue.prefix())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.prefix()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new CommonPrefix(prefix);
  }

  public static DafnySequence<? extends CommonPrefix> CommonPrefixList(
    List<software.amazon.awssdk.services.s3.model.CommonPrefix> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::CommonPrefix,
      CommonPrefix._typeDescriptor()
    );
  }

  public static Delete Delete(
    software.amazon.awssdk.services.s3.model.Delete nativeValue
  ) {
    DafnySequence<? extends ObjectIdentifier> objects;
    objects = ToDafny.ObjectIdentifierList(nativeValue.objects());
    Option<Boolean> quiet;
    quiet =
      Objects.nonNull(nativeValue.quiet())
        ? Option.create_Some(TypeDescriptor.BOOLEAN, (nativeValue.quiet()))
        : Option.create_None(TypeDescriptor.BOOLEAN);
    return new Delete(objects, quiet);
  }

  public static DeletedObject DeletedObject(
    software.amazon.awssdk.services.s3.model.DeletedObject nativeValue
  ) {
    Option<DafnySequence<? extends Character>> key;
    key =
      Objects.nonNull(nativeValue.key())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.key()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Boolean> deleteMarker;
    deleteMarker =
      Objects.nonNull(nativeValue.deleteMarker())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.deleteMarker())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> deleteMarkerVersionId;
    deleteMarkerVersionId =
      Objects.nonNull(nativeValue.deleteMarkerVersionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.deleteMarkerVersionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new DeletedObject(
      key,
      versionId,
      deleteMarker,
      deleteMarkerVersionId
    );
  }

  public static DafnySequence<? extends DeletedObject> DeletedObjects(
    List<software.amazon.awssdk.services.s3.model.DeletedObject> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::DeletedObject,
      DeletedObject._typeDescriptor()
    );
  }

  public static DeleteObjectOutput DeleteObjectOutput(
    DeleteObjectResponse nativeValue
  ) {
    Option<Boolean> deleteMarker;
    deleteMarker =
      Objects.nonNull(nativeValue.deleteMarker())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.deleteMarker())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestCharged> requestCharged;
    requestCharged =
      Objects.nonNull(nativeValue.requestCharged())
        ? Option.create_Some(
          RequestCharged._typeDescriptor(),
          ToDafny.RequestCharged(nativeValue.requestCharged())
        )
        : Option.create_None(RequestCharged._typeDescriptor());
    return new DeleteObjectOutput(deleteMarker, versionId, requestCharged);
  }

  public static DeleteObjectRequest DeleteObjectRequest(
    software.amazon.awssdk.services.s3.model.DeleteObjectRequest nativeValue
  ) {
    DafnySequence<? extends Character> bucket;
    bucket =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.bucket()
      );
    DafnySequence<? extends Character> key;
    key =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.key()
      );
    Option<DafnySequence<? extends Character>> mFA;
    mFA =
      Objects.nonNull(nativeValue.mfa())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.mfa()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestPayer> requestPayer;
    requestPayer =
      Objects.nonNull(nativeValue.requestPayer())
        ? Option.create_Some(
          RequestPayer._typeDescriptor(),
          ToDafny.RequestPayer(nativeValue.requestPayer())
        )
        : Option.create_None(RequestPayer._typeDescriptor());
    Option<Boolean> bypassGovernanceRetention;
    bypassGovernanceRetention =
      Objects.nonNull(nativeValue.bypassGovernanceRetention())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.bypassGovernanceRetention())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> expectedBucketOwner;
    expectedBucketOwner =
      Objects.nonNull(nativeValue.expectedBucketOwner())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expectedBucketOwner()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new DeleteObjectRequest(
      bucket,
      key,
      mFA,
      versionId,
      requestPayer,
      bypassGovernanceRetention,
      expectedBucketOwner
    );
  }

  public static DeleteObjectsOutput DeleteObjectsOutput(
    DeleteObjectsResponse nativeValue
  ) {
    Option<DafnySequence<? extends DeletedObject>> deleted;
    deleted =
      (Objects.nonNull(nativeValue.deleted()) &&
          nativeValue.deleted().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(DeletedObject._typeDescriptor()),
          ToDafny.DeletedObjects(nativeValue.deleted())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(DeletedObject._typeDescriptor())
        );
    Option<RequestCharged> requestCharged;
    requestCharged =
      Objects.nonNull(nativeValue.requestCharged())
        ? Option.create_Some(
          RequestCharged._typeDescriptor(),
          ToDafny.RequestCharged(nativeValue.requestCharged())
        )
        : Option.create_None(RequestCharged._typeDescriptor());
    Option<DafnySequence<? extends ErrorShape>> errors;
    errors =
      (Objects.nonNull(nativeValue.errors()) && nativeValue.errors().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(ErrorShape._typeDescriptor()),
          ToDafny.Errors(nativeValue.errors())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(ErrorShape._typeDescriptor())
        );
    return new DeleteObjectsOutput(deleted, requestCharged, errors);
  }

  public static DeleteObjectsRequest DeleteObjectsRequest(
    software.amazon.awssdk.services.s3.model.DeleteObjectsRequest nativeValue
  ) {
    DafnySequence<? extends Character> bucket;
    bucket =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.bucket()
      );
    Delete delete;
    delete = ToDafny.Delete(nativeValue.delete());
    Option<DafnySequence<? extends Character>> mFA;
    mFA =
      Objects.nonNull(nativeValue.mfa())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.mfa()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestPayer> requestPayer;
    requestPayer =
      Objects.nonNull(nativeValue.requestPayer())
        ? Option.create_Some(
          RequestPayer._typeDescriptor(),
          ToDafny.RequestPayer(nativeValue.requestPayer())
        )
        : Option.create_None(RequestPayer._typeDescriptor());
    Option<Boolean> bypassGovernanceRetention;
    bypassGovernanceRetention =
      Objects.nonNull(nativeValue.bypassGovernanceRetention())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.bypassGovernanceRetention())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> expectedBucketOwner;
    expectedBucketOwner =
      Objects.nonNull(nativeValue.expectedBucketOwner())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expectedBucketOwner()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ChecksumAlgorithm> checksumAlgorithm;
    checksumAlgorithm =
      Objects.nonNull(nativeValue.checksumAlgorithm())
        ? Option.create_Some(
          ChecksumAlgorithm._typeDescriptor(),
          ToDafny.ChecksumAlgorithm(nativeValue.checksumAlgorithm())
        )
        : Option.create_None(ChecksumAlgorithm._typeDescriptor());
    return new DeleteObjectsRequest(
      bucket,
      delete,
      mFA,
      requestPayer,
      bypassGovernanceRetention,
      expectedBucketOwner,
      checksumAlgorithm
    );
  }

  public static DafnySequence<? extends ErrorShape> Errors(
    List<software.amazon.awssdk.services.s3.model.S3Error> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::ErrorShape,
      ErrorShape._typeDescriptor()
    );
  }

  public static ErrorShape ErrorShape(
    software.amazon.awssdk.services.s3.model.S3Error nativeValue
  ) {
    Option<DafnySequence<? extends Character>> key;
    key =
      Objects.nonNull(nativeValue.key())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.key()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> code;
    code =
      Objects.nonNull(nativeValue.code())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.code()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> message;
    message =
      Objects.nonNull(nativeValue.message())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.message()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new ErrorShape(key, versionId, code, message);
  }

  public static GetObjectOutput GetObjectOutput(ResponseInputStream<GetObjectResponse> responseInputStream) {
    GetObjectResponse nativeValue = responseInputStream.response();
    Option<DataStream<Byte, Error>> body;
    body =
      Option.create_Some(
          null,
          new InputStreamAsDataStream<Error>(Error._typeDescriptor(), responseInputStream, e -> Error.create_Opaque(e))
        );
    Option<Boolean> deleteMarker;
    deleteMarker =
      Objects.nonNull(nativeValue.deleteMarker())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.deleteMarker())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> acceptRanges;
    acceptRanges =
      Objects.nonNull(nativeValue.acceptRanges())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.acceptRanges()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> expiration;
    expiration =
      Objects.nonNull(nativeValue.expiration())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expiration()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> restore;
    restore =
      Objects.nonNull(nativeValue.restore())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.restore()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> lastModified;
    lastModified =
      Objects.nonNull(nativeValue.lastModified())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.lastModified()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Long> contentLength;
    contentLength =
      Objects.nonNull(nativeValue.contentLength())
        ? Option.create_Some(TypeDescriptor.LONG, (nativeValue.contentLength()))
        : Option.create_None(TypeDescriptor.LONG);
    Option<DafnySequence<? extends Character>> eTag;
    eTag =
      Objects.nonNull(nativeValue.eTag())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.eTag()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumCRC32;
    checksumCRC32 =
      Objects.nonNull(nativeValue.checksumCRC32())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumCRC32C;
    checksumCRC32C =
      Objects.nonNull(nativeValue.checksumCRC32C())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32C()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA1;
    checksumSHA1 =
      Objects.nonNull(nativeValue.checksumSHA1())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA1()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA256;
    checksumSHA256 =
      Objects.nonNull(nativeValue.checksumSHA256())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA256()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Integer> missingMeta;
    missingMeta =
      Objects.nonNull(nativeValue.missingMeta())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.missingMeta()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> cacheControl;
    cacheControl =
      Objects.nonNull(nativeValue.cacheControl())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.cacheControl()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentDisposition;
    contentDisposition =
      Objects.nonNull(nativeValue.contentDisposition())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentDisposition()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentEncoding;
    contentEncoding =
      Objects.nonNull(nativeValue.contentEncoding())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentEncoding()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentLanguage;
    contentLanguage =
      Objects.nonNull(nativeValue.contentLanguage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentLanguage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentRange;
    contentRange =
      Objects.nonNull(nativeValue.contentRange())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentRange()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentType;
    contentType =
      Objects.nonNull(nativeValue.contentType())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentType()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> expires;
    expires =
      Objects.nonNull(nativeValue.expires())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expires()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> websiteRedirectLocation;
    websiteRedirectLocation =
      Objects.nonNull(nativeValue.websiteRedirectLocation())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.websiteRedirectLocation()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ServerSideEncryption> serverSideEncryption;
    serverSideEncryption =
      Objects.nonNull(nativeValue.serverSideEncryption())
        ? Option.create_Some(
          ServerSideEncryption._typeDescriptor(),
          ToDafny.ServerSideEncryption(nativeValue.serverSideEncryption())
        )
        : Option.create_None(ServerSideEncryption._typeDescriptor());
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > metadata;
    metadata =
      (Objects.nonNull(nativeValue.metadata()) &&
          nativeValue.metadata().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.Metadata(nativeValue.metadata())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<DafnySequence<? extends Character>> sSECustomerAlgorithm;
    sSECustomerAlgorithm =
      Objects.nonNull(nativeValue.sseCustomerAlgorithm())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerAlgorithm()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKeyMD5;
    sSECustomerKeyMD5 =
      Objects.nonNull(nativeValue.sseCustomerKeyMD5())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKeyMD5()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSEKMSKeyId;
    sSEKMSKeyId =
//      Objects.nonNull(nativeValue.sseKMSKeyId())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
//            nativeValue.sseKMSKeyId()
//          )
//        )
//        :
      Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Boolean> bucketKeyEnabled;
    bucketKeyEnabled =
      Objects.nonNull(nativeValue.bucketKeyEnabled())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.bucketKeyEnabled())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<StorageClass> storageClass;
    storageClass =
      Objects.nonNull(nativeValue.storageClass())
        ? Option.create_Some(
          StorageClass._typeDescriptor(),
          ToDafny.StorageClass(nativeValue.storageClass())
        )
        : Option.create_None(StorageClass._typeDescriptor());
    Option<RequestCharged> requestCharged;
    requestCharged =
      Objects.nonNull(nativeValue.requestCharged())
        ? Option.create_Some(
          RequestCharged._typeDescriptor(),
          ToDafny.RequestCharged(nativeValue.requestCharged())
        )
        : Option.create_None(RequestCharged._typeDescriptor());
    Option<ReplicationStatus> replicationStatus;
    replicationStatus =
      Objects.nonNull(nativeValue.replicationStatus())
        ? Option.create_Some(
          ReplicationStatus._typeDescriptor(),
          ToDafny.ReplicationStatus(nativeValue.replicationStatus())
        )
        : Option.create_None(ReplicationStatus._typeDescriptor());
    Option<Integer> partsCount;
    partsCount =
      Objects.nonNull(nativeValue.partsCount())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.partsCount()))
        : Option.create_None(TypeDescriptor.INT);
    Option<Integer> tagCount;
    tagCount =
      Objects.nonNull(nativeValue.tagCount())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.tagCount()))
        : Option.create_None(TypeDescriptor.INT);
    Option<ObjectLockMode> objectLockMode;
    objectLockMode =
      Objects.nonNull(nativeValue.objectLockMode())
        ? Option.create_Some(
          ObjectLockMode._typeDescriptor(),
          ToDafny.ObjectLockMode(nativeValue.objectLockMode())
        )
        : Option.create_None(ObjectLockMode._typeDescriptor());
    Option<DafnySequence<? extends Character>> objectLockRetainUntilDate;
    objectLockRetainUntilDate =
      Objects.nonNull(nativeValue.objectLockRetainUntilDate())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.objectLockRetainUntilDate()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ObjectLockLegalHoldStatus> objectLockLegalHoldStatus;
    objectLockLegalHoldStatus =
      Objects.nonNull(nativeValue.objectLockLegalHoldStatus())
        ? Option.create_Some(
          ObjectLockLegalHoldStatus._typeDescriptor(),
          ToDafny.ObjectLockLegalHoldStatus(
            nativeValue.objectLockLegalHoldStatus()
          )
        )
        : Option.create_None(ObjectLockLegalHoldStatus._typeDescriptor());
    return new GetObjectOutput(
      body,
      deleteMarker,
      acceptRanges,
      expiration,
      restore,
      lastModified,
      contentLength,
      eTag,
      checksumCRC32,
      checksumCRC32C,
      checksumSHA1,
      checksumSHA256,
      missingMeta,
      versionId,
      cacheControl,
      contentDisposition,
      contentEncoding,
      contentLanguage,
      contentRange,
      contentType,
      expires,
      websiteRedirectLocation,
      serverSideEncryption,
      metadata,
      sSECustomerAlgorithm,
      sSECustomerKeyMD5,
      sSEKMSKeyId,
      bucketKeyEnabled,
      storageClass,
      requestCharged,
      replicationStatus,
      partsCount,
      tagCount,
      objectLockMode,
      objectLockRetainUntilDate,
      objectLockLegalHoldStatus
    );
  }

  public static GetObjectRequest GetObjectRequest(
    software.amazon.awssdk.services.s3.model.GetObjectRequest nativeValue
  ) {
    DafnySequence<? extends Character> bucket;
    bucket =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.bucket()
      );
    Option<DafnySequence<? extends Character>> ifMatch;
    ifMatch =
      Objects.nonNull(nativeValue.ifMatch())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.ifMatch()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> ifModifiedSince;
    ifModifiedSince =
      Objects.nonNull(nativeValue.ifModifiedSince())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.ifModifiedSince()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> ifNoneMatch;
    ifNoneMatch =
      Objects.nonNull(nativeValue.ifNoneMatch())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.ifNoneMatch()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> ifUnmodifiedSince;
    ifUnmodifiedSince =
      Objects.nonNull(nativeValue.ifUnmodifiedSince())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.ifUnmodifiedSince()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    DafnySequence<? extends Character> key;
    key =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.key()
      );
    Option<DafnySequence<? extends Character>> range;
    range =
      Objects.nonNull(nativeValue.range())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.range()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseCacheControl;
    responseCacheControl =
      Objects.nonNull(nativeValue.responseCacheControl())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseCacheControl()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseContentDisposition;
    responseContentDisposition =
      Objects.nonNull(nativeValue.responseContentDisposition())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseContentDisposition()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseContentEncoding;
    responseContentEncoding =
      Objects.nonNull(nativeValue.responseContentEncoding())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseContentEncoding()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseContentLanguage;
    responseContentLanguage =
      Objects.nonNull(nativeValue.responseContentLanguage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseContentLanguage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseContentType;
    responseContentType =
      Objects.nonNull(nativeValue.responseContentType())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseContentType()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> responseExpires;
    responseExpires =
      Objects.nonNull(nativeValue.responseExpires())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.responseExpires()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerAlgorithm;
    sSECustomerAlgorithm =
      Objects.nonNull(nativeValue.sseCustomerAlgorithm())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerAlgorithm()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKey;
    sSECustomerKey =
      Objects.nonNull(nativeValue.sseCustomerKey())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKey()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKeyMD5;
    sSECustomerKeyMD5 =
      Objects.nonNull(nativeValue.sseCustomerKeyMD5())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKeyMD5()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestPayer> requestPayer;
    requestPayer =
      Objects.nonNull(nativeValue.requestPayer())
        ? Option.create_Some(
          RequestPayer._typeDescriptor(),
          ToDafny.RequestPayer(nativeValue.requestPayer())
        )
        : Option.create_None(RequestPayer._typeDescriptor());
    Option<Integer> partNumber;
    partNumber =
      Objects.nonNull(nativeValue.partNumber())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.partNumber()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Character>> expectedBucketOwner;
    expectedBucketOwner =
      Objects.nonNull(nativeValue.expectedBucketOwner())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expectedBucketOwner()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ChecksumMode> checksumMode;
    checksumMode =
      Objects.nonNull(nativeValue.checksumMode())
        ? Option.create_Some(
          ChecksumMode._typeDescriptor(),
          ToDafny.ChecksumMode(nativeValue.checksumMode())
        )
        : Option.create_None(ChecksumMode._typeDescriptor());
    return new GetObjectRequest(
      bucket,
      ifMatch,
      ifModifiedSince,
      ifNoneMatch,
      ifUnmodifiedSince,
      key,
      range,
      responseCacheControl,
      responseContentDisposition,
      responseContentEncoding,
      responseContentLanguage,
      responseContentType,
      responseExpires,
      versionId,
      sSECustomerAlgorithm,
      sSECustomerKey,
      sSECustomerKeyMD5,
      requestPayer,
      partNumber,
      expectedBucketOwner,
      checksumMode
    );
  }

  public static ListObjectsV2Output ListObjectsV2Output(
    ListObjectsV2Response nativeValue
  ) {
    Option<Boolean> isTruncated;
    isTruncated =
      Objects.nonNull(nativeValue.isTruncated())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.isTruncated())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends S3Object>> contents;
    contents =
      (Objects.nonNull(nativeValue.contents()) &&
          nativeValue.contents().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(S3Object._typeDescriptor()),
          ToDafny.ObjectList(nativeValue.contents())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(S3Object._typeDescriptor())
        );
    Option<DafnySequence<? extends Character>> name;
    name =
      Objects.nonNull(nativeValue.name())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.name()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> prefix;
    prefix =
      Objects.nonNull(nativeValue.prefix())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.prefix()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> delimiter;
    delimiter =
      Objects.nonNull(nativeValue.delimiter())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.delimiter()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Integer> maxKeys;
    maxKeys =
      Objects.nonNull(nativeValue.maxKeys())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.maxKeys()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends CommonPrefix>> commonPrefixes;
    commonPrefixes =
      (Objects.nonNull(nativeValue.commonPrefixes()) &&
          nativeValue.commonPrefixes().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(CommonPrefix._typeDescriptor()),
          ToDafny.CommonPrefixList(nativeValue.commonPrefixes())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(CommonPrefix._typeDescriptor())
        );
    Option<EncodingType> encodingType;
    encodingType =
      Objects.nonNull(nativeValue.encodingType())
        ? Option.create_Some(
          EncodingType._typeDescriptor(),
          ToDafny.EncodingType(nativeValue.encodingType())
        )
        : Option.create_None(EncodingType._typeDescriptor());
    Option<Integer> keyCount;
    keyCount =
      Objects.nonNull(nativeValue.keyCount())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.keyCount()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Character>> continuationToken;
    continuationToken =
      Objects.nonNull(nativeValue.continuationToken())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.continuationToken()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> nextContinuationToken;
    nextContinuationToken =
      Objects.nonNull(nativeValue.nextContinuationToken())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.nextContinuationToken()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> startAfter;
    startAfter =
      Objects.nonNull(nativeValue.startAfter())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.startAfter()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestCharged> requestCharged;
    requestCharged =
      Objects.nonNull(nativeValue.requestCharged())
        ? Option.create_Some(
          RequestCharged._typeDescriptor(),
          ToDafny.RequestCharged(nativeValue.requestCharged())
        )
        : Option.create_None(RequestCharged._typeDescriptor());
    return new ListObjectsV2Output(
      isTruncated,
      contents,
      name,
      prefix,
      delimiter,
      maxKeys,
      commonPrefixes,
      encodingType,
      keyCount,
      continuationToken,
      nextContinuationToken,
      startAfter,
      requestCharged
    );
  }

  public static ListObjectsV2Request ListObjectsV2Request(
    software.amazon.awssdk.services.s3.model.ListObjectsV2Request nativeValue
  ) {
    DafnySequence<? extends Character> bucket;
    bucket =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.bucket()
      );
    Option<DafnySequence<? extends Character>> delimiter;
    delimiter =
      Objects.nonNull(nativeValue.delimiter())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.delimiter()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<EncodingType> encodingType;
    encodingType =
      Objects.nonNull(nativeValue.encodingType())
        ? Option.create_Some(
          EncodingType._typeDescriptor(),
          ToDafny.EncodingType(nativeValue.encodingType())
        )
        : Option.create_None(EncodingType._typeDescriptor());
    Option<Integer> maxKeys;
    maxKeys =
      Objects.nonNull(nativeValue.maxKeys())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.maxKeys()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Character>> prefix;
    prefix =
      Objects.nonNull(nativeValue.prefix())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.prefix()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> continuationToken;
    continuationToken =
      Objects.nonNull(nativeValue.continuationToken())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.continuationToken()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Boolean> fetchOwner;
    fetchOwner =
      Objects.nonNull(nativeValue.fetchOwner())
        ? Option.create_Some(TypeDescriptor.BOOLEAN, (nativeValue.fetchOwner()))
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> startAfter;
    startAfter =
      Objects.nonNull(nativeValue.startAfter())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.startAfter()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<RequestPayer> requestPayer;
    requestPayer =
      Objects.nonNull(nativeValue.requestPayer())
        ? Option.create_Some(
          RequestPayer._typeDescriptor(),
          ToDafny.RequestPayer(nativeValue.requestPayer())
        )
        : Option.create_None(RequestPayer._typeDescriptor());
    Option<DafnySequence<? extends Character>> expectedBucketOwner;
    expectedBucketOwner =
      Objects.nonNull(nativeValue.expectedBucketOwner())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expectedBucketOwner()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<
      DafnySequence<? extends OptionalObjectAttributes>
    > optionalObjectAttributes;
    optionalObjectAttributes =
      (Objects.nonNull(nativeValue.optionalObjectAttributes()) &&
          nativeValue.optionalObjectAttributes().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            OptionalObjectAttributes._typeDescriptor()
          ),
          ToDafny.OptionalObjectAttributesList(
            nativeValue.optionalObjectAttributes()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            OptionalObjectAttributes._typeDescriptor()
          )
        );
    return new ListObjectsV2Request(
      bucket,
      delimiter,
      encodingType,
      maxKeys,
      prefix,
      continuationToken,
      fetchOwner,
      startAfter,
      requestPayer,
      expectedBucketOwner,
      optionalObjectAttributes
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Character>,
    ? extends DafnySequence<? extends Character>
  > Metadata(Map<String, String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
    );
  }

  public static S3Object Object(
    software.amazon.awssdk.services.s3.model.S3Object nativeValue
  ) {
    Option<DafnySequence<? extends Character>> key;
    key =
      Objects.nonNull(nativeValue.key())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.key()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> lastModified;
    lastModified =
      Objects.nonNull(nativeValue.lastModified())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.lastModified()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> eTag;
    eTag =
      Objects.nonNull(nativeValue.eTag())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.eTag()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends ChecksumAlgorithm>> checksumAlgorithm;
    checksumAlgorithm =
      (Objects.nonNull(nativeValue.checksumAlgorithm()) &&
          nativeValue.checksumAlgorithm().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(ChecksumAlgorithm._typeDescriptor()),
          ToDafny.ChecksumAlgorithmList(nativeValue.checksumAlgorithm())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(ChecksumAlgorithm._typeDescriptor())
        );
    Option<Long> size;
    size =
      Objects.nonNull(nativeValue.size())
        ? Option.create_Some(TypeDescriptor.LONG, (nativeValue.size()))
        : Option.create_None(TypeDescriptor.LONG);
    Option<ObjectStorageClass> storageClass;
    storageClass =
      Objects.nonNull(nativeValue.storageClass())
        ? Option.create_Some(
          ObjectStorageClass._typeDescriptor(),
          ToDafny.ObjectStorageClass(nativeValue.storageClass())
        )
        : Option.create_None(ObjectStorageClass._typeDescriptor());
    Option<Owner> owner;
    owner =
      Objects.nonNull(nativeValue.owner())
        ? Option.create_Some(
          Owner._typeDescriptor(),
          ToDafny.Owner(nativeValue.owner())
        )
        : Option.create_None(Owner._typeDescriptor());
    Option<RestoreStatus> restoreStatus;
    restoreStatus =
      Objects.nonNull(nativeValue.restoreStatus())
        ? Option.create_Some(
          RestoreStatus._typeDescriptor(),
          ToDafny.RestoreStatus(nativeValue.restoreStatus())
        )
        : Option.create_None(RestoreStatus._typeDescriptor());
    return new S3Object(
      key,
      lastModified,
      eTag,
      checksumAlgorithm,
      size,
      storageClass,
      owner,
      restoreStatus
    );
  }

  public static ObjectIdentifier ObjectIdentifier(
    software.amazon.awssdk.services.s3.model.ObjectIdentifier nativeValue
  ) {
    DafnySequence<? extends Character> key;
    key =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.key()
      );
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new ObjectIdentifier(key, versionId);
  }

  public static DafnySequence<? extends ObjectIdentifier> ObjectIdentifierList(
    List<software.amazon.awssdk.services.s3.model.ObjectIdentifier> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::ObjectIdentifier,
      ObjectIdentifier._typeDescriptor()
    );
  }

  public static DafnySequence<? extends S3Object> ObjectList(
    List<software.amazon.awssdk.services.s3.model.S3Object> nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::Object,
            S3Object._typeDescriptor()
    );
  }

  public static DafnySequence<
    ? extends OptionalObjectAttributes
  > OptionalObjectAttributesList(
    List<
      software.amazon.awssdk.services.s3.model.OptionalObjectAttributes
    > nativeValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.cryptography.services.s3.internaldafny.ToDafny::OptionalObjectAttributes,
      OptionalObjectAttributes._typeDescriptor()
    );
  }

  public static Owner Owner(
    software.amazon.awssdk.services.s3.model.Owner nativeValue
  ) {
    Option<DafnySequence<? extends Character>> displayName;
    displayName =
      Objects.nonNull(nativeValue.displayName())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.displayName()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> iD;
    iD =
      Objects.nonNull(nativeValue.id())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.id()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new Owner(displayName, iD);
  }

  public static PutObjectOutput PutObjectOutput(PutObjectResponse nativeValue) {
    Option<DafnySequence<? extends Character>> expiration;
    expiration =
      Objects.nonNull(nativeValue.expiration())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expiration()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> eTag;
    eTag =
      Objects.nonNull(nativeValue.eTag())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.eTag()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumCRC32;
    checksumCRC32 =
      Objects.nonNull(nativeValue.checksumCRC32())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumCRC32C;
    checksumCRC32C =
      Objects.nonNull(nativeValue.checksumCRC32C())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32C()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA1;
    checksumSHA1 =
      Objects.nonNull(nativeValue.checksumSHA1())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA1()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA256;
    checksumSHA256 =
      Objects.nonNull(nativeValue.checksumSHA256())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA256()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ServerSideEncryption> serverSideEncryption;
    serverSideEncryption =
      Objects.nonNull(nativeValue.serverSideEncryption())
        ? Option.create_Some(
          ServerSideEncryption._typeDescriptor(),
          ToDafny.ServerSideEncryption(nativeValue.serverSideEncryption())
        )
        : Option.create_None(ServerSideEncryption._typeDescriptor());
    Option<DafnySequence<? extends Character>> versionId;
    versionId =
      Objects.nonNull(nativeValue.versionId())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.versionId()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerAlgorithm;
    sSECustomerAlgorithm =
      Objects.nonNull(nativeValue.sseCustomerAlgorithm())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerAlgorithm()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKeyMD5;
    sSECustomerKeyMD5 =
      Objects.nonNull(nativeValue.sseCustomerKeyMD5())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKeyMD5()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSEKMSKeyId;
    sSEKMSKeyId =
//      Objects.nonNull(nativeValue.sseKMSKeyId())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
//            nativeValue.sseKMSKeyId()
//          )
//        )
//        :
      Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSEKMSEncryptionContext;
    sSEKMSEncryptionContext =
//      Objects.nonNull(nativeValue.sseKMSEncryptionContext())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
//            nativeValue.sseKMSEncryptionContext()
//          )
//        )
//        :
      Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Boolean> bucketKeyEnabled;
    bucketKeyEnabled =
      Objects.nonNull(nativeValue.bucketKeyEnabled())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.bucketKeyEnabled())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<RequestCharged> requestCharged;
    requestCharged =
      Objects.nonNull(nativeValue.requestCharged())
        ? Option.create_Some(
          RequestCharged._typeDescriptor(),
          ToDafny.RequestCharged(nativeValue.requestCharged())
        )
        : Option.create_None(RequestCharged._typeDescriptor());
    return new PutObjectOutput(
      expiration,
      eTag,
      checksumCRC32,
      checksumCRC32C,
      checksumSHA1,
      checksumSHA256,
      serverSideEncryption,
      versionId,
      sSECustomerAlgorithm,
      sSECustomerKeyMD5,
      sSEKMSKeyId,
      sSEKMSEncryptionContext,
      bucketKeyEnabled,
      requestCharged
    );
  }

  public static PutObjectRequest PutObjectRequest(
    software.amazon.awssdk.services.s3.model.PutObjectRequest nativeValue,
    RequestBody nativeBody
  ) {
    Option<ObjectCannedACL> aCL;
    aCL =
      Objects.nonNull(nativeValue.acl())
        ? Option.create_Some(
          ObjectCannedACL._typeDescriptor(),
          ToDafny.ObjectCannedACL(nativeValue.acl())
        )
        : Option.create_None(ObjectCannedACL._typeDescriptor());
    Option<DataStream<Byte, Error>> body = Option.create_Some(
            null,
            new RequestBodyAsDataStream(
            null, nativeBody, Error::create_Opaque    ));
//    body =
//      Objects.nonNull(nativeValue.body())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
//            nativeValue.body().asByteArray()
//          )
//        )
//        : Option.create_None(
//          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
//        );
    DafnySequence<? extends Character> bucket;
    bucket =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.bucket()
      );
    Option<DafnySequence<? extends Character>> cacheControl;
    cacheControl =
      Objects.nonNull(nativeValue.cacheControl())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.cacheControl()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentDisposition;
    contentDisposition =
      Objects.nonNull(nativeValue.contentDisposition())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentDisposition()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentEncoding;
    contentEncoding =
      Objects.nonNull(nativeValue.contentEncoding())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentEncoding()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentLanguage;
    contentLanguage =
      Objects.nonNull(nativeValue.contentLanguage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentLanguage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Long> contentLength;
    contentLength =
      Objects.nonNull(nativeValue.contentLength())
        ? Option.create_Some(TypeDescriptor.LONG, (nativeValue.contentLength()))
        : Option.create_None(TypeDescriptor.LONG);
    Option<DafnySequence<? extends Character>> contentMD5;
    contentMD5 =
      Objects.nonNull(nativeValue.contentMD5())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentMD5()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> contentType;
    contentType =
      Objects.nonNull(nativeValue.contentType())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.contentType()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ChecksumAlgorithm> checksumAlgorithm;
    checksumAlgorithm =
      Objects.nonNull(nativeValue.checksumAlgorithm())
        ? Option.create_Some(
          ChecksumAlgorithm._typeDescriptor(),
          ToDafny.ChecksumAlgorithm(nativeValue.checksumAlgorithm())
        )
        : Option.create_None(ChecksumAlgorithm._typeDescriptor());
    Option<DafnySequence<? extends Character>> checksumCRC32;
    checksumCRC32 =
      Objects.nonNull(nativeValue.checksumCRC32())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumCRC32C;
    checksumCRC32C =
      Objects.nonNull(nativeValue.checksumCRC32C())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumCRC32C()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA1;
    checksumSHA1 =
      Objects.nonNull(nativeValue.checksumSHA1())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA1()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> checksumSHA256;
    checksumSHA256 =
      Objects.nonNull(nativeValue.checksumSHA256())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.checksumSHA256()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> expires;
    expires =
      Objects.nonNull(nativeValue.expires())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expires()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> grantFullControl;
    grantFullControl =
      Objects.nonNull(nativeValue.grantFullControl())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.grantFullControl()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> grantRead;
    grantRead =
      Objects.nonNull(nativeValue.grantRead())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.grantRead()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> grantReadACP;
    grantReadACP =
      Objects.nonNull(nativeValue.grantReadACP())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.grantReadACP()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> grantWriteACP;
    grantWriteACP =
      Objects.nonNull(nativeValue.grantWriteACP())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.grantWriteACP()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    DafnySequence<? extends Character> key;
    key =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.key()
      );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > metadata;
    metadata =
      (Objects.nonNull(nativeValue.metadata()) &&
          nativeValue.metadata().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.Metadata(nativeValue.metadata())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<ServerSideEncryption> serverSideEncryption;
    serverSideEncryption =
      Objects.nonNull(nativeValue.serverSideEncryption())
        ? Option.create_Some(
          ServerSideEncryption._typeDescriptor(),
          ToDafny.ServerSideEncryption(nativeValue.serverSideEncryption())
        )
        : Option.create_None(ServerSideEncryption._typeDescriptor());
    Option<StorageClass> storageClass;
    storageClass =
      Objects.nonNull(nativeValue.storageClass())
        ? Option.create_Some(
          StorageClass._typeDescriptor(),
          ToDafny.StorageClass(nativeValue.storageClass())
        )
        : Option.create_None(StorageClass._typeDescriptor());
    Option<DafnySequence<? extends Character>> websiteRedirectLocation;
    websiteRedirectLocation =
      Objects.nonNull(nativeValue.websiteRedirectLocation())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.websiteRedirectLocation()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerAlgorithm;
    sSECustomerAlgorithm =
      Objects.nonNull(nativeValue.sseCustomerAlgorithm())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerAlgorithm()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKey;
    sSECustomerKey =
      Objects.nonNull(nativeValue.sseCustomerKey())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKey()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSECustomerKeyMD5;
    sSECustomerKeyMD5 =
      Objects.nonNull(nativeValue.sseCustomerKeyMD5())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.sseCustomerKeyMD5()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSEKMSKeyId;
    sSEKMSKeyId =
//      Objects.nonNull(nativeValue.sseKMSKeyId())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
//            nativeValue.sseKMSKeyId()
//          )
//        )
//        :
      Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> sSEKMSEncryptionContext;
    sSEKMSEncryptionContext =
//      Objects.nonNull(nativeValue.sseKMSEncryptionContext())
//        ? Option.create_Some(
//          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
//          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
//            nativeValue.sseKMSEncryptionContext()
//          )
//        )
//        :
      Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<Boolean> bucketKeyEnabled;
    bucketKeyEnabled =
      Objects.nonNull(nativeValue.bucketKeyEnabled())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.bucketKeyEnabled())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<RequestPayer> requestPayer;
    requestPayer =
      Objects.nonNull(nativeValue.requestPayer())
        ? Option.create_Some(
          RequestPayer._typeDescriptor(),
          ToDafny.RequestPayer(nativeValue.requestPayer())
        )
        : Option.create_None(RequestPayer._typeDescriptor());
    Option<DafnySequence<? extends Character>> tagging;
    tagging =
      Objects.nonNull(nativeValue.tagging())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.tagging()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ObjectLockMode> objectLockMode;
    objectLockMode =
      Objects.nonNull(nativeValue.objectLockMode())
        ? Option.create_Some(
          ObjectLockMode._typeDescriptor(),
          ToDafny.ObjectLockMode(nativeValue.objectLockMode())
        )
        : Option.create_None(ObjectLockMode._typeDescriptor());
    Option<DafnySequence<? extends Character>> objectLockRetainUntilDate;
    objectLockRetainUntilDate =
      Objects.nonNull(nativeValue.objectLockRetainUntilDate())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.objectLockRetainUntilDate()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<ObjectLockLegalHoldStatus> objectLockLegalHoldStatus;
    objectLockLegalHoldStatus =
      Objects.nonNull(nativeValue.objectLockLegalHoldStatus())
        ? Option.create_Some(
          ObjectLockLegalHoldStatus._typeDescriptor(),
          ToDafny.ObjectLockLegalHoldStatus(
            nativeValue.objectLockLegalHoldStatus()
          )
        )
        : Option.create_None(ObjectLockLegalHoldStatus._typeDescriptor());
    Option<DafnySequence<? extends Character>> expectedBucketOwner;
    expectedBucketOwner =
      Objects.nonNull(nativeValue.expectedBucketOwner())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.expectedBucketOwner()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new PutObjectRequest(
      aCL,
      body,
      bucket,
      cacheControl,
      contentDisposition,
      contentEncoding,
      contentLanguage,
      contentLength,
      contentMD5,
      contentType,
      checksumAlgorithm,
      checksumCRC32,
      checksumCRC32C,
      checksumSHA1,
      checksumSHA256,
      expires,
      grantFullControl,
      grantRead,
      grantReadACP,
      grantWriteACP,
      key,
      metadata,
      serverSideEncryption,
      storageClass,
      websiteRedirectLocation,
      sSECustomerAlgorithm,
      sSECustomerKey,
      sSECustomerKeyMD5,
      sSEKMSKeyId,
      sSEKMSEncryptionContext,
      bucketKeyEnabled,
      requestPayer,
      tagging,
      objectLockMode,
      objectLockRetainUntilDate,
      objectLockLegalHoldStatus,
      expectedBucketOwner
    );
  }

  public static RestoreStatus RestoreStatus(
    software.amazon.awssdk.services.s3.model.RestoreStatus nativeValue
  ) {
    Option<Boolean> isRestoreInProgress;
    isRestoreInProgress =
      Objects.nonNull(nativeValue.isRestoreInProgress())
        ? Option.create_Some(
          TypeDescriptor.BOOLEAN,
          (nativeValue.isRestoreInProgress())
        )
        : Option.create_None(TypeDescriptor.BOOLEAN);
    Option<DafnySequence<? extends Character>> restoreExpiryDate;
    restoreExpiryDate =
      Objects.nonNull(nativeValue.restoreExpiryDate())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.restoreExpiryDate()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new RestoreStatus(isRestoreInProgress, restoreExpiryDate);
  }

  public static Error Error(InvalidObjectStateException nativeValue) {
    Option<StorageClass> storageClass;
    storageClass =
      Objects.nonNull(nativeValue.storageClass())
        ? Option.create_Some(
          StorageClass._typeDescriptor(),
          ToDafny.StorageClass(nativeValue.storageClass())
        )
        : Option.create_None(StorageClass._typeDescriptor());
    Option<IntelligentTieringAccessTier> accessTier;
    accessTier =
      Objects.nonNull(nativeValue.accessTier())
        ? Option.create_Some(
          IntelligentTieringAccessTier._typeDescriptor(),
          ToDafny.IntelligentTieringAccessTier(nativeValue.accessTier())
        )
        : Option.create_None(IntelligentTieringAccessTier._typeDescriptor());
    Option<DafnySequence<? extends Character>> message;
    message =
      Objects.nonNull(nativeValue.getMessage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.getMessage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new Error_InvalidObjectState(storageClass, accessTier, message);
  }

  public static Error Error(NoSuchBucketException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message =
      Objects.nonNull(nativeValue.getMessage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.getMessage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new Error_NoSuchBucket(message);
  }

  public static Error Error(NoSuchKeyException nativeValue) {
    Option<DafnySequence<? extends Character>> message;
    message =
      Objects.nonNull(nativeValue.getMessage())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.getMessage()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    return new Error_NoSuchKey(message);
  }

  public static ChecksumAlgorithm ChecksumAlgorithm(
    software.amazon.awssdk.services.s3.model.ChecksumAlgorithm nativeValue
  ) {
    switch (nativeValue) {
      case CRC32:
        {
          return ChecksumAlgorithm.create_CRC32();
        }
      case CRC32_C:
        {
          return ChecksumAlgorithm.create_CRC32C();
        }
      case SHA1:
        {
          return ChecksumAlgorithm.create_SHA1();
        }
      case SHA256:
        {
          return ChecksumAlgorithm.create_SHA256();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ChecksumAlgorithm."
          );
        }
    }
  }

  public static ChecksumMode ChecksumMode(
    software.amazon.awssdk.services.s3.model.ChecksumMode nativeValue
  ) {
    switch (nativeValue) {
      case ENABLED:
        {
          return ChecksumMode.create();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ChecksumMode."
          );
        }
    }
  }

  public static EncodingType EncodingType(
    software.amazon.awssdk.services.s3.model.EncodingType nativeValue
  ) {
    switch (nativeValue) {
      case URL:
        {
          return EncodingType.create();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.EncodingType."
          );
        }
    }
  }

  public static IntelligentTieringAccessTier IntelligentTieringAccessTier(
    software.amazon.awssdk.services.s3.model.IntelligentTieringAccessTier nativeValue
  ) {
    switch (nativeValue) {
      case ARCHIVE_ACCESS:
        {
          return IntelligentTieringAccessTier.create_ARCHIVE__ACCESS();
        }
      case DEEP_ARCHIVE_ACCESS:
        {
          return IntelligentTieringAccessTier.create_DEEP__ARCHIVE__ACCESS();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.IntelligentTieringAccessTier."
          );
        }
    }
  }

  public static ObjectCannedACL ObjectCannedACL(
    software.amazon.awssdk.services.s3.model.ObjectCannedACL nativeValue
  ) {
    switch (nativeValue) {
      case PRIVATE:
        {
          return ObjectCannedACL.create_private();
        }
      case PUBLIC_READ:
        {
          return ObjectCannedACL.create_public__read();
        }
      case PUBLIC_READ_WRITE:
        {
          return ObjectCannedACL.create_public__read__write();
        }
      case AUTHENTICATED_READ:
        {
          return ObjectCannedACL.create_authenticated__read();
        }
      case AWS_EXEC_READ:
        {
          return ObjectCannedACL.create_aws__exec__read();
        }
      case BUCKET_OWNER_READ:
        {
          return ObjectCannedACL.create_bucket__owner__read();
        }
      case BUCKET_OWNER_FULL_CONTROL:
        {
          return ObjectCannedACL.create_bucket__owner__full__control();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ObjectCannedACL."
          );
        }
    }
  }

  public static ObjectLockLegalHoldStatus ObjectLockLegalHoldStatus(
    software.amazon.awssdk.services.s3.model.ObjectLockLegalHoldStatus nativeValue
  ) {
    switch (nativeValue) {
      case ON:
        {
          return ObjectLockLegalHoldStatus.create_ON();
        }
      case OFF:
        {
          return ObjectLockLegalHoldStatus.create_OFF();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockLegalHoldStatus."
          );
        }
    }
  }

  public static ObjectLockMode ObjectLockMode(
    software.amazon.awssdk.services.s3.model.ObjectLockMode nativeValue
  ) {
    switch (nativeValue) {
      case GOVERNANCE:
        {
          return ObjectLockMode.create_GOVERNANCE();
        }
      case COMPLIANCE:
        {
          return ObjectLockMode.create_COMPLIANCE();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockMode."
          );
        }
    }
  }

  public static ObjectStorageClass ObjectStorageClass(
    software.amazon.awssdk.services.s3.model.ObjectStorageClass nativeValue
  ) {
    switch (nativeValue) {
      case STANDARD:
        {
          return ObjectStorageClass.create_STANDARD();
        }
      case REDUCED_REDUNDANCY:
        {
          return ObjectStorageClass.create_REDUCED__REDUNDANCY();
        }
      case GLACIER:
        {
          return ObjectStorageClass.create_GLACIER();
        }
      case STANDARD_IA:
        {
          return ObjectStorageClass.create_STANDARD__IA();
        }
      case ONEZONE_IA:
        {
          return ObjectStorageClass.create_ONEZONE__IA();
        }
      case INTELLIGENT_TIERING:
        {
          return ObjectStorageClass.create_INTELLIGENT__TIERING();
        }
      case DEEP_ARCHIVE:
        {
          return ObjectStorageClass.create_DEEP__ARCHIVE();
        }
      case OUTPOSTS:
        {
          return ObjectStorageClass.create_OUTPOSTS();
        }
      case GLACIER_IR:
        {
          return ObjectStorageClass.create_GLACIER__IR();
        }
      case SNOW:
        {
          return ObjectStorageClass.create_SNOW();
        }
      case EXPRESS_ONEZONE:
        {
          return ObjectStorageClass.create_EXPRESS__ONEZONE();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ObjectStorageClass."
          );
        }
    }
  }

  public static OptionalObjectAttributes OptionalObjectAttributes(
    software.amazon.awssdk.services.s3.model.OptionalObjectAttributes nativeValue
  ) {
    switch (nativeValue) {
      case RESTORE_STATUS:
        {
          return OptionalObjectAttributes.create();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.OptionalObjectAttributes."
          );
        }
    }
  }

  public static ReplicationStatus ReplicationStatus(
    software.amazon.awssdk.services.s3.model.ReplicationStatus nativeValue
  ) {
    switch (nativeValue) {
      case COMPLETE:
        {
          return ReplicationStatus.create_COMPLETE();
        }
      case PENDING:
        {
          return ReplicationStatus.create_PENDING();
        }
      case FAILED:
        {
          return ReplicationStatus.create_FAILED();
        }
      case REPLICA:
        {
          return ReplicationStatus.create_REPLICA();
        }
      case COMPLETED:
        {
          return ReplicationStatus.create_COMPLETED();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ReplicationStatus."
          );
        }
    }
  }

  public static RequestCharged RequestCharged(
    software.amazon.awssdk.services.s3.model.RequestCharged nativeValue
  ) {
    switch (nativeValue) {
      case REQUESTER:
        {
          return RequestCharged.create();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.RequestCharged."
          );
        }
    }
  }

  public static RequestPayer RequestPayer(
    software.amazon.awssdk.services.s3.model.RequestPayer nativeValue
  ) {
    switch (nativeValue) {
      case REQUESTER:
        {
          return RequestPayer.create();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.RequestPayer."
          );
        }
    }
  }

  public static ServerSideEncryption ServerSideEncryption(
    software.amazon.awssdk.services.s3.model.ServerSideEncryption nativeValue
  ) {
    switch (nativeValue) {
      case AES256:
        {
          return ServerSideEncryption.create_AES256();
        }
      case AWS_KMS:
        {
          return ServerSideEncryption.create_aws__kms();
        }
      case AWS_KMS_DSSE:
        {
          return ServerSideEncryption.create_aws__kms__dsse();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.ServerSideEncryption."
          );
        }
    }
  }

  public static StorageClass StorageClass(
    software.amazon.awssdk.services.s3.model.StorageClass nativeValue
  ) {
    switch (nativeValue) {
      case STANDARD:
        {
          return StorageClass.create_STANDARD();
        }
      case REDUCED_REDUNDANCY:
        {
          return StorageClass.create_REDUCED__REDUNDANCY();
        }
      case STANDARD_IA:
        {
          return StorageClass.create_STANDARD__IA();
        }
      case ONEZONE_IA:
        {
          return StorageClass.create_ONEZONE__IA();
        }
      case INTELLIGENT_TIERING:
        {
          return StorageClass.create_INTELLIGENT__TIERING();
        }
      case GLACIER:
        {
          return StorageClass.create_GLACIER();
        }
      case DEEP_ARCHIVE:
        {
          return StorageClass.create_DEEP__ARCHIVE();
        }
      case OUTPOSTS:
        {
          return StorageClass.create_OUTPOSTS();
        }
      case GLACIER_IR:
        {
          return StorageClass.create_GLACIER__IR();
        }
      case SNOW:
        {
          return StorageClass.create_SNOW();
        }
      case EXPRESS_ONEZONE:
        {
          return StorageClass.create_EXPRESS__ONEZONE();
        }
      default:
        {
          throw new RuntimeException(
            "Cannot convert " +
            nativeValue +
            " to software.amazon.cryptography.services.s3.internaldafny.types.StorageClass."
          );
        }
    }
  }

  public static ChecksumAlgorithm ChecksumAlgorithm(String nativeValue) {
    return ChecksumAlgorithm(
      software.amazon.awssdk.services.s3.model.ChecksumAlgorithm.fromValue(
        nativeValue
      )
    );
  }

  public static ChecksumMode ChecksumMode(String nativeValue) {
    return ChecksumMode(
      software.amazon.awssdk.services.s3.model.ChecksumMode.fromValue(
        nativeValue
      )
    );
  }

  public static EncodingType EncodingType(String nativeValue) {
    return EncodingType(
      software.amazon.awssdk.services.s3.model.EncodingType.fromValue(
        nativeValue
      )
    );
  }

  public static IntelligentTieringAccessTier IntelligentTieringAccessTier(
    String nativeValue
  ) {
    return IntelligentTieringAccessTier(
      software.amazon.awssdk.services.s3.model.IntelligentTieringAccessTier.fromValue(
        nativeValue
      )
    );
  }

  public static ObjectCannedACL ObjectCannedACL(String nativeValue) {
    return ObjectCannedACL(
      software.amazon.awssdk.services.s3.model.ObjectCannedACL.fromValue(
        nativeValue
      )
    );
  }

  public static ObjectLockLegalHoldStatus ObjectLockLegalHoldStatus(
    String nativeValue
  ) {
    return ObjectLockLegalHoldStatus(
      software.amazon.awssdk.services.s3.model.ObjectLockLegalHoldStatus.fromValue(
        nativeValue
      )
    );
  }

  public static ObjectLockMode ObjectLockMode(String nativeValue) {
    return ObjectLockMode(
      software.amazon.awssdk.services.s3.model.ObjectLockMode.fromValue(
        nativeValue
      )
    );
  }

  public static ObjectStorageClass ObjectStorageClass(String nativeValue) {
    return ObjectStorageClass(
      software.amazon.awssdk.services.s3.model.ObjectStorageClass.fromValue(
        nativeValue
      )
    );
  }

  public static OptionalObjectAttributes OptionalObjectAttributes(
    String nativeValue
  ) {
    return OptionalObjectAttributes(
      software.amazon.awssdk.services.s3.model.OptionalObjectAttributes.fromValue(
        nativeValue
      )
    );
  }

  public static ReplicationStatus ReplicationStatus(String nativeValue) {
    return ReplicationStatus(
      software.amazon.awssdk.services.s3.model.ReplicationStatus.fromValue(
        nativeValue
      )
    );
  }

  public static RequestCharged RequestCharged(String nativeValue) {
    return RequestCharged(
      software.amazon.awssdk.services.s3.model.RequestCharged.fromValue(
        nativeValue
      )
    );
  }

  public static RequestPayer RequestPayer(String nativeValue) {
    return RequestPayer(
      software.amazon.awssdk.services.s3.model.RequestPayer.fromValue(
        nativeValue
      )
    );
  }

  public static ServerSideEncryption ServerSideEncryption(String nativeValue) {
    return ServerSideEncryption(
      software.amazon.awssdk.services.s3.model.ServerSideEncryption.fromValue(
        nativeValue
      )
    );
  }

  public static StorageClass StorageClass(String nativeValue) {
    return StorageClass(
      software.amazon.awssdk.services.s3.model.StorageClass.fromValue(
        nativeValue
      )
    );
  }

  public static Error Error(S3Exception nativeValue) {
    // While this is logically identical to the other Opaque Error case,
    // it is semantically distinct.
    // An un-modeled Service Error is different from a Java Heap Exhaustion error.
    // In the future, Smithy-Dafny MAY allow for this distinction.
    // Which would allow Dafny developers to treat the two differently.
    return Error.create_OpaqueWithText(
      nativeValue,
      dafny.DafnySequence.asString(nativeValue.getMessage())
    );
  }

  public static Error Error(Exception nativeValue) {
    // While this is logically identical to the other Opaque Error case,
    // it is semantically distinct.
    // An un-modeled Service Error is different from a Java Heap Exhaustion error.
    // In the future, Smithy-Dafny MAY allow for this distinction.
    // Which would allow Dafny developers to treat the two differently.
    return Error.create_OpaqueWithText(
      nativeValue,
      dafny.DafnySequence.asString(nativeValue.getMessage())
    );
  }

  public static IS3Client AmazonS3(S3Client nativeValue) {
    return new Shim(nativeValue, null);
  }
}
