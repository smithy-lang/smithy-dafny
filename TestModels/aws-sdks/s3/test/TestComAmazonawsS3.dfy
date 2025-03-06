// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3
    import opened StandardLibrary.UInt
    import opened Wrappers
    import opened Std.Enumerators
    import opened Std.Aggregators
    import opened Std.Streams

    const testBucket := "s3-dafny-test-bucket"
    const testObjectKey := "smithy-dafny-test-model-object-key"

    method {:test} BasicRoundTripTests() {
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            )
        );
        // Note the chunk size has to ensure all but the last chunk is >= 8192 bytes.
        // For a small stream like this that means just one chunk.
        var s: ByteStream := new SeqByteStream([ 97, 115, 100, 102 ], 10);
        expect s is RewindableByteStream;
        PutObjectTest(
            input := S3.Types.PutObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey,
                Body := Wrappers.Some(s)
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
        nameonly expectedBody: BoundedInts.bytes
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.GetObject(input);

        expect(ret.Success?);

        // we only care about the Body
        var MyBody := ret.value.Body;
        expect MyBody.Some?;

        // TODO: These need to be generated as postconditions on GetObject instead
        assume {:axiom} fresh(MyBody.value.Repr);
        assume {:axiom} MyBody.value.Valid();
        
        var bodyValue := Collect(MyBody.value);
        expect bodyValue == expectedBody;
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

        expect ret.Success?, ret;

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

    method Collect(e: ByteStream) returns (s: BoundedInts.bytes) 
        requires e.Valid()
        modifies e.Repr
    {
        var a := new Collector();
        ForEach(e, a);
        return Seq.Flatten(a.values);
    }
}
