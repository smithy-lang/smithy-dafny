// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3
    import opened Wrappers

    const testBucket := "smithy-dafny-s3-test-bucket"
    const testObjectKey := "test-model-object-key"

    method {:test} BasicRoundTripTests() {
        PutObjectTest(
            input := S3.Types.PutObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey,
                Body := Wrappers.Some([ 97, 115, 100, 102 ])
            )
        );
    }

    // for now, just call put object, manually verify in S3 console
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
