// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3

    const testBucket := "smithy-dafny-s3-test-bucket";
    const testObjectKey := "test-model-object-key"

    method {:test} BasicRoundTripTests() {
        PutObjectTest(
            input := S3.Types.PutObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey,
                Body := [ 97, 115, 100, 102 ]
                // might need to pass Wrappers.None for extra params?
            )
        );
    }

    // for now, just call put object, manually verify in S3 console
    method PutObjectTest(
        nameonly input: S3.Types.PutObjectRequest
    )
    {
        var client := expect S3.S3Client();

        var ret := client.Decrypt(input);

        expect(ret.Success?);

        // TODO: unpack ret.value into PutObjectResponse
    }
}
