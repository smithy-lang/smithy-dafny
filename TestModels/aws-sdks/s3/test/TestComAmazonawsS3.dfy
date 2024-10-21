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
        var client :- expect S3.S3Client();
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            ),
            s3Client := client
        );
        PutObjectTest(
            input := S3.Types.PutObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey,
                Body := Wrappers.Some([ 97, 115, 100, 102 ])
            ),
            s3Client := client
        );
        GetObjectTest(
            input := S3.Types.GetObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            ),
            expectedBody := ([ 97, 115, 100, 102 ]),
            s3Client := client
        );
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            ),
            s3Client := client
        );
        GetObjectTestFailureNoSuchKey(
            input := S3.Types.GetObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            ),
            s3Client := client
        );
    }

    method GetObjectTest(
        nameonly input: S3.Types.GetObjectRequest,
        nameonly expectedBody: S3.Types.StreamingBlob,
        nameonly s3Client: S3.Types.IS3Client
    )
    {
        var ret := s3Client.GetObject(input);

        expect(ret.Success?);

        // we only care about the Body
        var MyBody := ret.value.Body;
        expect MyBody.Some?;
        expect MyBody.value == expectedBody;
    }

    method GetObjectTestFailureNoSuchKey(
        nameonly input: S3.Types.GetObjectRequest,
        nameonly s3Client: S3.Types.IS3Client
    )
    {
        var ret := s3Client.GetObject(input);

        expect ret.Failure?;
        // TODO: this fails in CI..?
        // expect ret.error.NoSuchKey?;
    }

    method PutObjectTest(
        nameonly input: S3.Types.PutObjectRequest,
        nameonly s3Client: S3.Types.IS3Client
    )
    {
        var ret := s3Client.PutObject(input);

        expect(ret.Success?);

        // just check that an ETag was returned
        var MyETag := ret.value.ETag;

        expect MyETag.Some?;
    }

    method DeleteObjectTest(
        nameonly input: S3.Types.DeleteObjectRequest,
        nameonly s3Client: S3.Types.IS3Client
    )
    {
        var ret := s3Client.DeleteObject(input);

        expect(ret.Success?);
    }
}
