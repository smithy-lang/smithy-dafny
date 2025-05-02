// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.services.s3.internaldafny;

import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Character;
import java.lang.IllegalStateException;
import java.lang.RuntimeException;
import java.lang.String;
import java.lang.Throwable;
import java.util.List;
import java.util.Map;
import software.amazon.awssdk.core.SdkBytes;
import software.amazon.awssdk.services.s3.S3Client;
import software.amazon.awssdk.services.s3.model.ChecksumAlgorithm;
import software.amazon.awssdk.services.s3.model.ChecksumMode;
import software.amazon.awssdk.services.s3.model.Delete;
import software.amazon.awssdk.services.s3.model.DeleteObjectRequest;
import software.amazon.awssdk.services.s3.model.DeleteObjectResponse;
import software.amazon.awssdk.services.s3.model.DeleteObjectsRequest;
import software.amazon.awssdk.services.s3.model.DeleteObjectsResponse;
import software.amazon.awssdk.services.s3.model.DeletedObject;
import software.amazon.awssdk.services.s3.model.GetObjectRequest;
import software.amazon.awssdk.services.s3.model.GetObjectResponse;
import software.amazon.awssdk.services.s3.model.IntelligentTieringAccessTier;
import software.amazon.awssdk.services.s3.model.InvalidObjectStateException;
import software.amazon.awssdk.services.s3.model.NoSuchBucketException;
import software.amazon.awssdk.services.s3.model.NoSuchKeyException;
import software.amazon.awssdk.services.s3.model.ObjectCannedACL;
import software.amazon.awssdk.services.s3.model.ObjectIdentifier;
import software.amazon.awssdk.services.s3.model.ObjectLockLegalHoldStatus;
import software.amazon.awssdk.services.s3.model.ObjectLockMode;
import software.amazon.awssdk.services.s3.model.PutObjectRequest;
import software.amazon.awssdk.services.s3.model.PutObjectResponse;
import software.amazon.awssdk.services.s3.model.ReplicationStatus;
import software.amazon.awssdk.services.s3.model.RequestCharged;
import software.amazon.awssdk.services.s3.model.RequestPayer;
import software.amazon.awssdk.services.s3.model.S3Error;
import software.amazon.awssdk.services.s3.model.S3Exception;
import software.amazon.awssdk.services.s3.model.ServerSideEncryption;
import software.amazon.awssdk.services.s3.model.StorageClass;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.Error;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_InvalidObjectState;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_NoSuchBucket;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_NoSuchKey;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_Opaque;
import software.amazon.cryptography.services.s3.internaldafny.types.Error_OpaqueWithText;
import software.amazon.cryptography.services.s3.internaldafny.types.GetObjectOutput;
import software.amazon.cryptography.services.s3.internaldafny.types.IS3Client;
import software.amazon.cryptography.services.s3.internaldafny.types.PutObjectOutput;

public class ToNative {

  public static ChecksumAlgorithm ChecksumAlgorithm(
    software.amazon.cryptography.services.s3.internaldafny.types.ChecksumAlgorithm dafnyValue
  ) {
    if (dafnyValue.is_CRC32()) {
      return ChecksumAlgorithm.CRC32;
    }
    if (dafnyValue.is_CRC32C()) {
      return ChecksumAlgorithm.CRC32_C;
    }
    if (dafnyValue.is_SHA1()) {
      return ChecksumAlgorithm.SHA1;
    }
    if (dafnyValue.is_SHA256()) {
      return ChecksumAlgorithm.SHA256;
    }
    return ChecksumAlgorithm.fromValue(dafnyValue.toString());
  }

  public static ChecksumMode ChecksumMode(
    software.amazon.cryptography.services.s3.internaldafny.types.ChecksumMode dafnyValue
  ) {
    if (dafnyValue.is_ENABLED()) {
      return ChecksumMode.ENABLED;
    }
    return ChecksumMode.fromValue(dafnyValue.toString());
  }

  public static Delete Delete(
    software.amazon.cryptography.services.s3.internaldafny.types.Delete dafnyValue
  ) {
    Delete.Builder builder = Delete.builder();
    builder.objects(ToNative.ObjectIdentifierList(dafnyValue.dtor_Objects()));
    if (dafnyValue.dtor_Quiet().is_Some()) {
      builder.quiet((dafnyValue.dtor_Quiet().dtor_value()));
    }
    return builder.build();
  }

  public static DeletedObject DeletedObject(
    software.amazon.cryptography.services.s3.internaldafny.types.DeletedObject dafnyValue
  ) {
    DeletedObject.Builder builder = DeletedObject.builder();
    if (dafnyValue.dtor_DeleteMarker().is_Some()) {
      builder.deleteMarker((dafnyValue.dtor_DeleteMarker().dtor_value()));
    }
    if (dafnyValue.dtor_DeleteMarkerVersionId().is_Some()) {
      builder.deleteMarkerVersionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_DeleteMarkerVersionId().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Key().is_Some()) {
      builder.key(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Key().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static List<DeletedObject> DeletedObjects(
    DafnySequence<
      ? extends software.amazon.cryptography.services.s3.internaldafny.types.DeletedObject
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.cryptography.services.s3.internaldafny.ToNative::DeletedObject
    );
  }

  public static DeleteObjectResponse DeleteObjectOutput(
    DeleteObjectOutput dafnyValue
  ) {
    DeleteObjectResponse.Builder builder = DeleteObjectResponse.builder();
    if (dafnyValue.dtor_DeleteMarker().is_Some()) {
      builder.deleteMarker((dafnyValue.dtor_DeleteMarker().dtor_value()));
    }
    if (dafnyValue.dtor_RequestCharged().is_Some()) {
      builder.requestCharged(
        ToNative.RequestCharged(dafnyValue.dtor_RequestCharged().dtor_value())
      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static DeleteObjectRequest DeleteObjectRequest(
    software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectRequest dafnyValue
  ) {
    DeleteObjectRequest.Builder builder = DeleteObjectRequest.builder();
    builder.bucket(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Bucket()
      )
    );
    if (dafnyValue.dtor_BypassGovernanceRetention().is_Some()) {
      builder.bypassGovernanceRetention(
        (dafnyValue.dtor_BypassGovernanceRetention().dtor_value())
      );
    }
    if (dafnyValue.dtor_ExpectedBucketOwner().is_Some()) {
      builder.expectedBucketOwner(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ExpectedBucketOwner().dtor_value()
        )
      );
    }
    builder.key(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Key()
      )
    );
    if (dafnyValue.dtor_MFA().is_Some()) {
      builder.mfa(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_MFA().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestPayer().is_Some()) {
      builder.requestPayer(
        ToNative.RequestPayer(dafnyValue.dtor_RequestPayer().dtor_value())
      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static DeleteObjectsResponse DeleteObjectsOutput(
    DeleteObjectsOutput dafnyValue
  ) {
    DeleteObjectsResponse.Builder builder = DeleteObjectsResponse.builder();
    if (dafnyValue.dtor_Deleted().is_Some()) {
      builder.deleted(
        ToNative.DeletedObjects(dafnyValue.dtor_Deleted().dtor_value())
      );
    }
    if (dafnyValue.dtor_Errors().is_Some()) {
      builder.errors(ToNative.Errors(dafnyValue.dtor_Errors().dtor_value()));
    }
    if (dafnyValue.dtor_RequestCharged().is_Some()) {
      builder.requestCharged(
        ToNative.RequestCharged(dafnyValue.dtor_RequestCharged().dtor_value())
      );
    }
    return builder.build();
  }

  public static DeleteObjectsRequest DeleteObjectsRequest(
    software.amazon.cryptography.services.s3.internaldafny.types.DeleteObjectsRequest dafnyValue
  ) {
    DeleteObjectsRequest.Builder builder = DeleteObjectsRequest.builder();
    builder.bucket(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Bucket()
      )
    );
    if (dafnyValue.dtor_BypassGovernanceRetention().is_Some()) {
      builder.bypassGovernanceRetention(
        (dafnyValue.dtor_BypassGovernanceRetention().dtor_value())
      );
    }
    if (dafnyValue.dtor_ChecksumAlgorithm().is_Some()) {
      builder.checksumAlgorithm(
        ToNative.ChecksumAlgorithm(
          dafnyValue.dtor_ChecksumAlgorithm().dtor_value()
        )
      );
    }
    builder.delete(ToNative.Delete(dafnyValue.dtor_Delete()));
    if (dafnyValue.dtor_ExpectedBucketOwner().is_Some()) {
      builder.expectedBucketOwner(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ExpectedBucketOwner().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MFA().is_Some()) {
      builder.mfa(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_MFA().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestPayer().is_Some()) {
      builder.requestPayer(
        ToNative.RequestPayer(dafnyValue.dtor_RequestPayer().dtor_value())
      );
    }
    return builder.build();
  }

  public static List<S3Error> Errors(
    DafnySequence<
      ? extends software.amazon.cryptography.services.s3.internaldafny.types.ErrorShape
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.cryptography.services.s3.internaldafny.ToNative::ErrorShape
    );
  }

  public static S3Error ErrorShape(
    software.amazon.cryptography.services.s3.internaldafny.types.ErrorShape dafnyValue
  ) {
    S3Error.Builder builder = S3Error.builder();
    if (dafnyValue.dtor_Code().is_Some()) {
      builder.code(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Code().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Key().is_Some()) {
      builder.key(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Key().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Message().is_Some()) {
      builder.message(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Message().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static GetObjectResponse GetObjectOutput(GetObjectOutput dafnyValue) {
    GetObjectResponse.Builder builder = GetObjectResponse.builder();
    if (dafnyValue.dtor_AcceptRanges().is_Some()) {
      builder.acceptRanges(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_AcceptRanges().dtor_value()
        )
      );
    }
//    if (dafnyValue.dtor_Body().is_Some()) {
//      builder.body(
//        SdkBytes.fromByteArray(
//          (byte[]) (dafnyValue.dtor_Body().dtor_value().toRawArray())
//        )
//      );
//    }
    if (dafnyValue.dtor_BucketKeyEnabled().is_Some()) {
      builder.bucketKeyEnabled(
        (dafnyValue.dtor_BucketKeyEnabled().dtor_value())
      );
    }
    if (dafnyValue.dtor_CacheControl().is_Some()) {
      builder.cacheControl(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_CacheControl().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32().is_Some()) {
      builder.checksumCRC32(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32C().is_Some()) {
      builder.checksumCRC32C(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32C().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA1().is_Some()) {
      builder.checksumSHA1(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA1().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA256().is_Some()) {
      builder.checksumSHA256(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA256().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentDisposition().is_Some()) {
      builder.contentDisposition(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentDisposition().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentEncoding().is_Some()) {
      builder.contentEncoding(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentEncoding().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentLanguage().is_Some()) {
      builder.contentLanguage(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentLanguage().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentLength().is_Some()) {
      builder.contentLength((dafnyValue.dtor_ContentLength().dtor_value()));
    }
    if (dafnyValue.dtor_ContentRange().is_Some()) {
      builder.contentRange(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentRange().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentType().is_Some()) {
      builder.contentType(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentType().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_DeleteMarker().is_Some()) {
      builder.deleteMarker((dafnyValue.dtor_DeleteMarker().dtor_value()));
    }
    if (dafnyValue.dtor_ETag().is_Some()) {
      builder.eTag(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ETag().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Expiration().is_Some()) {
      builder.expiration(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Expiration().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Expires().is_Some()) {
      builder.expires(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_Expires().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_LastModified().is_Some()) {
      builder.lastModified(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_LastModified().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Metadata().is_Some()) {
      builder.metadata(
        ToNative.Metadata(dafnyValue.dtor_Metadata().dtor_value())
      );
    }
    if (dafnyValue.dtor_MissingMeta().is_Some()) {
      builder.missingMeta((dafnyValue.dtor_MissingMeta().dtor_value()));
    }
    if (dafnyValue.dtor_ObjectLockLegalHoldStatus().is_Some()) {
      builder.objectLockLegalHoldStatus(
        ToNative.ObjectLockLegalHoldStatus(
          dafnyValue.dtor_ObjectLockLegalHoldStatus().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ObjectLockMode().is_Some()) {
      builder.objectLockMode(
        ToNative.ObjectLockMode(dafnyValue.dtor_ObjectLockMode().dtor_value())
      );
    }
    if (dafnyValue.dtor_ObjectLockRetainUntilDate().is_Some()) {
      builder.objectLockRetainUntilDate(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_ObjectLockRetainUntilDate().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_PartsCount().is_Some()) {
      builder.partsCount((dafnyValue.dtor_PartsCount().dtor_value()));
    }
    if (dafnyValue.dtor_ReplicationStatus().is_Some()) {
      builder.replicationStatus(
        ToNative.ReplicationStatus(
          dafnyValue.dtor_ReplicationStatus().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestCharged().is_Some()) {
      builder.requestCharged(
        ToNative.RequestCharged(dafnyValue.dtor_RequestCharged().dtor_value())
      );
    }
    if (dafnyValue.dtor_Restore().is_Some()) {
      builder.restore(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Restore().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ServerSideEncryption().is_Some()) {
      builder.serverSideEncryption(
        ToNative.ServerSideEncryption(
          dafnyValue.dtor_ServerSideEncryption().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerAlgorithm().is_Some()) {
      builder.sseCustomerAlgorithm(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerAlgorithm().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKeyMD5().is_Some()) {
      builder.sseCustomerKeyMD5(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKeyMD5().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSEKMSKeyId().is_Some()) {
//      builder.sseKMSKeyId(
//        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
//          dafnyValue.dtor_SSEKMSKeyId().dtor_value()
//        )
//      );
    }
    if (dafnyValue.dtor_StorageClass().is_Some()) {
      builder.storageClass(
        ToNative.StorageClass(dafnyValue.dtor_StorageClass().dtor_value())
      );
    }
    if (dafnyValue.dtor_TagCount().is_Some()) {
      builder.tagCount((dafnyValue.dtor_TagCount().dtor_value()));
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_WebsiteRedirectLocation().is_Some()) {
      builder.websiteRedirectLocation(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_WebsiteRedirectLocation().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static GetObjectRequest GetObjectRequest(
    software.amazon.cryptography.services.s3.internaldafny.types.GetObjectRequest dafnyValue
  ) {
    GetObjectRequest.Builder builder = GetObjectRequest.builder();
    builder.bucket(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Bucket()
      )
    );
    if (dafnyValue.dtor_ChecksumMode().is_Some()) {
      builder.checksumMode(
        ToNative.ChecksumMode(dafnyValue.dtor_ChecksumMode().dtor_value())
      );
    }
    if (dafnyValue.dtor_ExpectedBucketOwner().is_Some()) {
      builder.expectedBucketOwner(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ExpectedBucketOwner().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_IfMatch().is_Some()) {
      builder.ifMatch(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_IfMatch().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_IfModifiedSince().is_Some()) {
      builder.ifModifiedSince(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_IfModifiedSince().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_IfNoneMatch().is_Some()) {
      builder.ifNoneMatch(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_IfNoneMatch().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_IfUnmodifiedSince().is_Some()) {
      builder.ifUnmodifiedSince(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_IfUnmodifiedSince().dtor_value()
        )
      );
    }
    builder.key(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Key()
      )
    );
    if (dafnyValue.dtor_PartNumber().is_Some()) {
      builder.partNumber((dafnyValue.dtor_PartNumber().dtor_value()));
    }
    if (dafnyValue.dtor_Range().is_Some()) {
      builder.range(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Range().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestPayer().is_Some()) {
      builder.requestPayer(
        ToNative.RequestPayer(dafnyValue.dtor_RequestPayer().dtor_value())
      );
    }
    if (dafnyValue.dtor_ResponseCacheControl().is_Some()) {
      builder.responseCacheControl(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ResponseCacheControl().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ResponseContentDisposition().is_Some()) {
      builder.responseContentDisposition(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ResponseContentDisposition().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ResponseContentEncoding().is_Some()) {
      builder.responseContentEncoding(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ResponseContentEncoding().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ResponseContentLanguage().is_Some()) {
      builder.responseContentLanguage(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ResponseContentLanguage().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ResponseContentType().is_Some()) {
      builder.responseContentType(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ResponseContentType().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ResponseExpires().is_Some()) {
      builder.responseExpires(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_ResponseExpires().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerAlgorithm().is_Some()) {
      builder.sseCustomerAlgorithm(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerAlgorithm().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKey().is_Some()) {
      builder.sseCustomerKey(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKey().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKeyMD5().is_Some()) {
      builder.sseCustomerKeyMD5(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKeyMD5().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static IntelligentTieringAccessTier IntelligentTieringAccessTier(
    software.amazon.cryptography.services.s3.internaldafny.types.IntelligentTieringAccessTier dafnyValue
  ) {
    if (dafnyValue.is_ARCHIVE__ACCESS()) {
      return IntelligentTieringAccessTier.ARCHIVE_ACCESS;
    }
    if (dafnyValue.is_DEEP__ARCHIVE__ACCESS()) {
      return IntelligentTieringAccessTier.DEEP_ARCHIVE_ACCESS;
    }
    return IntelligentTieringAccessTier.fromValue(dafnyValue.toString());
  }

  public static Map<String, String> Metadata(
    DafnyMap<
      ? extends DafnySequence<? extends Character>,
      ? extends DafnySequence<? extends Character>
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static ObjectCannedACL ObjectCannedACL(
    software.amazon.cryptography.services.s3.internaldafny.types.ObjectCannedACL dafnyValue
  ) {
    if (dafnyValue.is_private()) {
      return ObjectCannedACL.PRIVATE;
    }
    if (dafnyValue.is_public__read()) {
      return ObjectCannedACL.PUBLIC_READ;
    }
    if (dafnyValue.is_public__read__write()) {
      return ObjectCannedACL.PUBLIC_READ_WRITE;
    }
    if (dafnyValue.is_authenticated__read()) {
      return ObjectCannedACL.AUTHENTICATED_READ;
    }
    if (dafnyValue.is_aws__exec__read()) {
      return ObjectCannedACL.AWS_EXEC_READ;
    }
    if (dafnyValue.is_bucket__owner__read()) {
      return ObjectCannedACL.BUCKET_OWNER_READ;
    }
    if (dafnyValue.is_bucket__owner__full__control()) {
      return ObjectCannedACL.BUCKET_OWNER_FULL_CONTROL;
    }
    return ObjectCannedACL.fromValue(dafnyValue.toString());
  }

  public static ObjectIdentifier ObjectIdentifier(
    software.amazon.cryptography.services.s3.internaldafny.types.ObjectIdentifier dafnyValue
  ) {
    ObjectIdentifier.Builder builder = ObjectIdentifier.builder();
    builder.key(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Key()
      )
    );
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static List<ObjectIdentifier> ObjectIdentifierList(
    DafnySequence<
      ? extends software.amazon.cryptography.services.s3.internaldafny.types.ObjectIdentifier
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.cryptography.services.s3.internaldafny.ToNative::ObjectIdentifier
    );
  }

  public static ObjectLockLegalHoldStatus ObjectLockLegalHoldStatus(
    software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockLegalHoldStatus dafnyValue
  ) {
    if (dafnyValue.is_ON()) {
      return ObjectLockLegalHoldStatus.ON;
    }
    if (dafnyValue.is_OFF()) {
      return ObjectLockLegalHoldStatus.OFF;
    }
    return ObjectLockLegalHoldStatus.fromValue(dafnyValue.toString());
  }

  public static ObjectLockMode ObjectLockMode(
    software.amazon.cryptography.services.s3.internaldafny.types.ObjectLockMode dafnyValue
  ) {
    if (dafnyValue.is_GOVERNANCE()) {
      return ObjectLockMode.GOVERNANCE;
    }
    if (dafnyValue.is_COMPLIANCE()) {
      return ObjectLockMode.COMPLIANCE;
    }
    return ObjectLockMode.fromValue(dafnyValue.toString());
  }

  public static PutObjectResponse PutObjectOutput(PutObjectOutput dafnyValue) {
    PutObjectResponse.Builder builder = PutObjectResponse.builder();
    if (dafnyValue.dtor_BucketKeyEnabled().is_Some()) {
      builder.bucketKeyEnabled(
        (dafnyValue.dtor_BucketKeyEnabled().dtor_value())
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32().is_Some()) {
      builder.checksumCRC32(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32C().is_Some()) {
      builder.checksumCRC32C(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32C().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA1().is_Some()) {
      builder.checksumSHA1(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA1().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA256().is_Some()) {
      builder.checksumSHA256(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA256().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ETag().is_Some()) {
      builder.eTag(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ETag().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Expiration().is_Some()) {
      builder.expiration(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Expiration().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestCharged().is_Some()) {
      builder.requestCharged(
        ToNative.RequestCharged(dafnyValue.dtor_RequestCharged().dtor_value())
      );
    }
    if (dafnyValue.dtor_ServerSideEncryption().is_Some()) {
      builder.serverSideEncryption(
        ToNative.ServerSideEncryption(
          dafnyValue.dtor_ServerSideEncryption().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerAlgorithm().is_Some()) {
      builder.sseCustomerAlgorithm(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerAlgorithm().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKeyMD5().is_Some()) {
      builder.sseCustomerKeyMD5(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKeyMD5().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSEKMSEncryptionContext().is_Some()) {
//      builder.sseKMSEncryptionContext(
//        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
//          dafnyValue.dtor_SSEKMSEncryptionContext().dtor_value()
//        )
//      );
    }
    if (dafnyValue.dtor_SSEKMSKeyId().is_Some()) {
//      builder.sseKMSKeyId(
//        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
//          dafnyValue.dtor_SSEKMSKeyId().dtor_value()
//        )
//      );
    }
    if (dafnyValue.dtor_VersionId().is_Some()) {
      builder.versionId(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_VersionId().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static PutObjectRequest PutObjectRequest(
    software.amazon.cryptography.services.s3.internaldafny.types.PutObjectRequest dafnyValue
  ) {
    PutObjectRequest.Builder builder = PutObjectRequest.builder();
    if (dafnyValue.dtor_ACL().is_Some()) {
      builder.acl(ToNative.ObjectCannedACL(dafnyValue.dtor_ACL().dtor_value()));
    }
//    if (dafnyValue.dtor_Body().is_Some()) {
//      builder.body(
//        SdkBytes.fromByteArray(
//          (byte[]) (dafnyValue.dtor_Body().dtor_value().toRawArray())
//        )
//      );
//    }
    builder.bucket(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Bucket()
      )
    );
    if (dafnyValue.dtor_BucketKeyEnabled().is_Some()) {
      builder.bucketKeyEnabled(
        (dafnyValue.dtor_BucketKeyEnabled().dtor_value())
      );
    }
    if (dafnyValue.dtor_CacheControl().is_Some()) {
      builder.cacheControl(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_CacheControl().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumAlgorithm().is_Some()) {
      builder.checksumAlgorithm(
        ToNative.ChecksumAlgorithm(
          dafnyValue.dtor_ChecksumAlgorithm().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32().is_Some()) {
      builder.checksumCRC32(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumCRC32C().is_Some()) {
      builder.checksumCRC32C(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumCRC32C().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA1().is_Some()) {
      builder.checksumSHA1(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA1().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ChecksumSHA256().is_Some()) {
      builder.checksumSHA256(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ChecksumSHA256().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentDisposition().is_Some()) {
      builder.contentDisposition(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentDisposition().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentEncoding().is_Some()) {
      builder.contentEncoding(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentEncoding().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentLanguage().is_Some()) {
      builder.contentLanguage(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentLanguage().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentLength().is_Some()) {
      builder.contentLength((dafnyValue.dtor_ContentLength().dtor_value()));
    }
    if (dafnyValue.dtor_ContentMD5().is_Some()) {
      builder.contentMD5(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentMD5().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ContentType().is_Some()) {
      builder.contentType(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ContentType().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ExpectedBucketOwner().is_Some()) {
      builder.expectedBucketOwner(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_ExpectedBucketOwner().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_Expires().is_Some()) {
      builder.expires(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_Expires().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_GrantFullControl().is_Some()) {
      builder.grantFullControl(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_GrantFullControl().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_GrantRead().is_Some()) {
      builder.grantRead(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_GrantRead().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_GrantReadACP().is_Some()) {
      builder.grantReadACP(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_GrantReadACP().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_GrantWriteACP().is_Some()) {
      builder.grantWriteACP(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_GrantWriteACP().dtor_value()
        )
      );
    }
    builder.key(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_Key()
      )
    );
    if (dafnyValue.dtor_Metadata().is_Some()) {
      builder.metadata(
        ToNative.Metadata(dafnyValue.dtor_Metadata().dtor_value())
      );
    }
    if (dafnyValue.dtor_ObjectLockLegalHoldStatus().is_Some()) {
      builder.objectLockLegalHoldStatus(
        ToNative.ObjectLockLegalHoldStatus(
          dafnyValue.dtor_ObjectLockLegalHoldStatus().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_ObjectLockMode().is_Some()) {
      builder.objectLockMode(
        ToNative.ObjectLockMode(dafnyValue.dtor_ObjectLockMode().dtor_value())
      );
    }
    if (dafnyValue.dtor_ObjectLockRetainUntilDate().is_Some()) {
      builder.objectLockRetainUntilDate(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.Instant(
          dafnyValue.dtor_ObjectLockRetainUntilDate().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_RequestPayer().is_Some()) {
      builder.requestPayer(
        ToNative.RequestPayer(dafnyValue.dtor_RequestPayer().dtor_value())
      );
    }
    if (dafnyValue.dtor_ServerSideEncryption().is_Some()) {
      builder.serverSideEncryption(
        ToNative.ServerSideEncryption(
          dafnyValue.dtor_ServerSideEncryption().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerAlgorithm().is_Some()) {
      builder.sseCustomerAlgorithm(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerAlgorithm().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKey().is_Some()) {
      builder.sseCustomerKey(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKey().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_SSECustomerKeyMD5().is_Some()) {
      builder.sseCustomerKeyMD5(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_SSECustomerKeyMD5().dtor_value()
        )
      );
    }
//    if (dafnyValue.dtor_SSEKMSEncryptionContext().is_Some()) {
//      builder.sseKMSEncryptionContext(
//        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
//          dafnyValue.dtor_SSEKMSEncryptionContext().dtor_value()
//        )
//      );
//    }
//    if (dafnyValue.dtor_SSEKMSKeyId().is_Some()) {
//      builder.sseKMSKeyId(
//        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
//          dafnyValue.dtor_SSEKMSKeyId().dtor_value()
//        )
//      );
//    }
    if (dafnyValue.dtor_StorageClass().is_Some()) {
      builder.storageClass(
        ToNative.StorageClass(dafnyValue.dtor_StorageClass().dtor_value())
      );
    }
    if (dafnyValue.dtor_Tagging().is_Some()) {
      builder.tagging(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_Tagging().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_WebsiteRedirectLocation().is_Some()) {
      builder.websiteRedirectLocation(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_WebsiteRedirectLocation().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static ReplicationStatus ReplicationStatus(
    software.amazon.cryptography.services.s3.internaldafny.types.ReplicationStatus dafnyValue
  ) {
    if (dafnyValue.is_COMPLETE()) {
      return ReplicationStatus.COMPLETE;
    }
    if (dafnyValue.is_PENDING()) {
      return ReplicationStatus.PENDING;
    }
    if (dafnyValue.is_FAILED()) {
      return ReplicationStatus.FAILED;
    }
    if (dafnyValue.is_REPLICA()) {
      return ReplicationStatus.REPLICA;
    }
    if (dafnyValue.is_COMPLETED()) {
      return ReplicationStatus.COMPLETED;
    }
    return ReplicationStatus.fromValue(dafnyValue.toString());
  }

  public static RequestCharged RequestCharged(
    software.amazon.cryptography.services.s3.internaldafny.types.RequestCharged dafnyValue
  ) {
    if (dafnyValue.is_requester()) {
      return RequestCharged.REQUESTER;
    }
    return RequestCharged.fromValue(dafnyValue.toString());
  }

  public static RequestPayer RequestPayer(
    software.amazon.cryptography.services.s3.internaldafny.types.RequestPayer dafnyValue
  ) {
    if (dafnyValue.is_requester()) {
      return RequestPayer.REQUESTER;
    }
    return RequestPayer.fromValue(dafnyValue.toString());
  }

  public static ServerSideEncryption ServerSideEncryption(
    software.amazon.cryptography.services.s3.internaldafny.types.ServerSideEncryption dafnyValue
  ) {
    if (dafnyValue.is_AES256()) {
      return ServerSideEncryption.AES256;
    }
    if (dafnyValue.is_aws__kms()) {
      return ServerSideEncryption.AWS_KMS;
    }
    if (dafnyValue.is_aws__kms__dsse()) {
      return ServerSideEncryption.AWS_KMS_DSSE;
    }
    return ServerSideEncryption.fromValue(dafnyValue.toString());
  }

  public static StorageClass StorageClass(
    software.amazon.cryptography.services.s3.internaldafny.types.StorageClass dafnyValue
  ) {
    if (dafnyValue.is_STANDARD()) {
      return StorageClass.STANDARD;
    }
    if (dafnyValue.is_REDUCED__REDUNDANCY()) {
      return StorageClass.REDUCED_REDUNDANCY;
    }
    if (dafnyValue.is_STANDARD__IA()) {
      return StorageClass.STANDARD_IA;
    }
    if (dafnyValue.is_ONEZONE__IA()) {
      return StorageClass.ONEZONE_IA;
    }
    if (dafnyValue.is_INTELLIGENT__TIERING()) {
      return StorageClass.INTELLIGENT_TIERING;
    }
    if (dafnyValue.is_GLACIER()) {
      return StorageClass.GLACIER;
    }
    if (dafnyValue.is_DEEP__ARCHIVE()) {
      return StorageClass.DEEP_ARCHIVE;
    }
    if (dafnyValue.is_OUTPOSTS()) {
      return StorageClass.OUTPOSTS;
    }
    if (dafnyValue.is_GLACIER__IR()) {
      return StorageClass.GLACIER_IR;
    }
    if (dafnyValue.is_SNOW()) {
      return StorageClass.SNOW;
    }
    if (dafnyValue.is_EXPRESS__ONEZONE()) {
      return StorageClass.EXPRESS_ONEZONE;
    }
    return StorageClass.fromValue(dafnyValue.toString());
  }

  public static InvalidObjectStateException Error(
    Error_InvalidObjectState dafnyValue
  ) {
    InvalidObjectStateException.Builder builder =
      InvalidObjectStateException.builder();
    if (dafnyValue.dtor_AccessTier().is_Some()) {
      builder.accessTier(
        ToNative.IntelligentTieringAccessTier(
          dafnyValue.dtor_AccessTier().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_message().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_StorageClass().is_Some()) {
      builder.storageClass(
        ToNative.StorageClass(dafnyValue.dtor_StorageClass().dtor_value())
      );
    }
    return builder.build();
  }

  public static NoSuchBucketException Error(Error_NoSuchBucket dafnyValue) {
    NoSuchBucketException.Builder builder = NoSuchBucketException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_message().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static NoSuchKeyException Error(Error_NoSuchKey dafnyValue) {
    NoSuchKeyException.Builder builder = NoSuchKeyException.builder();
    if (dafnyValue.dtor_message().is_Some()) {
      builder.message(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_message().dtor_value()
        )
      );
    }
    return builder.build();
  }

  public static S3Client AmazonS3(IS3Client dafnyValue) {
    return ((Shim) dafnyValue).impl();
  }

  public static RuntimeException Error(Error_Opaque dafnyValue) {
    // While the first two cases are logically identical,
    // there is a semantic distinction.
    // An un-modeled Service Error is different from a Java Heap Exhaustion error.
    // In the future, Smithy-Dafny MAY allow for this distinction.
    // Which would allow Dafny developers to treat the two differently.
    if (dafnyValue.dtor_obj() instanceof S3Exception) {
      return (S3Exception) dafnyValue.dtor_obj();
    } else if (dafnyValue.dtor_obj() instanceof RuntimeException) {
      return (RuntimeException) dafnyValue.dtor_obj();
    } else if (dafnyValue.dtor_obj() instanceof Throwable) {
      return new RuntimeException(
        String.format(
          "Unknown error thrown while calling Amazon Simple Storage Service. %s",
          (Throwable) dafnyValue.dtor_obj()
        )
      );
    }
    return new IllegalStateException(
      String.format(
        "Unknown error thrown while calling Amazon Simple Storage Service. %s",
        dafnyValue
      )
    );
  }

  public static RuntimeException Error(Error_OpaqueWithText dafnyValue) {
    // While the first two cases are logically identical,
    // there is a semantic distinction.
    // An un-modeled Service Error is different from a Java Heap Exhaustion error.
    // In the future, Smithy-Dafny MAY allow for this distinction.
    // Which would allow Dafny developers to treat the two differently.
    if (dafnyValue.dtor_obj() instanceof S3Exception) {
      return (S3Exception) dafnyValue.dtor_obj();
    } else if (dafnyValue.dtor_obj() instanceof RuntimeException) {
      return (RuntimeException) dafnyValue.dtor_obj();
    } else if (dafnyValue.dtor_obj() instanceof Throwable) {
      return new RuntimeException(
        String.format(
          "Unknown error thrown while calling Amazon Simple Storage Service. %s",
          (Throwable) dafnyValue.dtor_obj()
        )
      );
    }
    return new IllegalStateException(
      String.format(
        "Unknown error thrown while calling Amazon Simple Storage Service. %s",
        dafnyValue
      )
    );
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_InvalidObjectState()) {
      return ToNative.Error((Error_InvalidObjectState) dafnyValue);
    }
    if (dafnyValue.is_NoSuchBucket()) {
      return ToNative.Error((Error_NoSuchBucket) dafnyValue);
    }
    if (dafnyValue.is_NoSuchKey()) {
      return ToNative.Error((Error_NoSuchKey) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_OpaqueWithText()) {
      return ToNative.Error((Error_OpaqueWithText) dafnyValue);
    }
    // TODO This should indicate a codegen bug; every error Should have been taken care of.
    return new IllegalStateException(
      String.format(
        "Unknown error thrown while calling service. %s",
        dafnyValue
      )
    );
  }
}
