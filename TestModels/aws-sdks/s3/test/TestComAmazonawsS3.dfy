// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3
    import opened StandardLibrary.UInt
    import opened Wrappers

    const testBucket := "smithy-dafny-s3-test-bucket"
    const testObjectKey := "test-model-object-key-2"

    method {:test} BasicRoundTripTests() {
        PutObjectTest(
            input := S3.Types.PutObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey,
                Body := Wrappers.Some([ 97, 115, 100, 102 ])
            )
        );
        GetObjectTest(
            input := S3.Types.GetObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            ),
            expectedBody := ([ 97, 115, 100, 102 ])
        );
    }

    method GetObjectTest(
        nameonly input: S3.Types.GetObjectRequest,
        nameonly expectedBody: S3.Types.StreamingBlob
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.GetObject(input);

        expect(ret.Success?);

        var GetObjectOutput(MyBody, MyDeleteMarker, MyAcceptRanges, MyExpiration, MyRestore, MyModified, MyContentLength, 
            MyETag, MyChecksumCRC32, MyChecksumCRC32C, MyChecksumSHA1, MyChecksumSHA256, MyMissingMeta, MyVersionId, MyCacheControl, 
            MyContentDisposition, MyContentEncoding, MyContentLanguage, MyContentRange, MyContentType, MyExpires, MyWebsiteRedirectLocation, 
            MyServerSideEncryption, MyMetadata, MySSECustomerAlgorithm, MySSECustomerKeyMD5, MySSEKMSKeyId, MyBucketKeyEnabled, MyStorageClass, MyRequestCharged, 
            MyReplicationStatus, MyPartsCount, MyTagCount, MyObjectLockMode, MyObjectLockRetainUntilDate, MyObjectLockLegalHoldStatus) := ret.value;
        expect MyBody.Some?;
        var byteString := MyBody.value[0];
        expect MyBody.value == expectedBody;
    }

    method PutObjectTest(
        nameonly input: S3.Types.PutObjectRequest
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.PutObject(input);

        expect(ret.Success?);

        var PutObjectOutput(MyExpiration, MyETag, MyChecksumCRC32, MyChecksumCRC32C, MyChecksumSHA1, 
            MyChecksumSHA256, MyServerSideEncryption, MyVersionId, MySSECustomerAlgorithm, MySSECustomerKeyMD5, 
            MySSEKMSKeyId, MySSEKMSEncryptionContext, MyBucketKeyEnabled, MyRequestCharged) := ret.value;

        expect MyETag.Some?;
    }
}
