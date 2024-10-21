// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3
    import opened StandardLibrary.UInt
    import opened Wrappers

    const testBucket := "s3-dafny-test-bucket"
    const testObjectKey := "smithy-dafny-test-model-object-key"

    method {:test} BasicRoundTripTests() {
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            )
        );
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
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            )
        );
        GetObjectTestFailureNoSuchKey(
            input := S3.Types.GetObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            )
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

        // we only care about the Body
        var MyBody := ret.value.Body;
        expect MyBody.Some?;
        expect MyBody.value == expectedBody;
    }

    method GetObjectTestFailureNoSuchKey(
        nameonly input: S3.Types.GetObjectRequest
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.GetObject(input);

        expect ret.Failure?;
        expect ret.error.NoSuchKey?;
    }

    method PutObjectTest(
        nameonly input: S3.Types.PutObjectRequest
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.PutObject(input);

        expect(ret.Success?);

        // just check that an ETag was returned
        var MyETag := ret.value.ETag;

        expect MyETag.Some?;
    }

    method DeleteObjectTest(
        nameonly input: S3.Types.DeleteObjectRequest
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.DeleteObject(input);

        expect(ret.Success?);
    }
}
