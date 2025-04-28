// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsS3 {
    import Com.Amazonaws.S3
    import opened ComAmazonawsS3Types
    import opened StandardLibrary.UInt
    import opened StandardLibrary.Streams
    import opened Wrappers
    import opened Std.BulkActions
    import opened Std.Producers
    import opened Std.Consumers


    const testBucket := "s3-dafny-test-bucket"
    const testObjectKey := "smithy-dafny-test-model-object-key"

    method {:test} BasicRoundTripTests() {
        DeleteObjectTest(
            input := S3.Types.DeleteObjectRequest(
                Bucket := testBucket,
                Key := testObjectKey
            )
        );
        var s: DataStream := new SeqDataStream([ 97, 115, 100, 102 ]);
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
        nameonly expectedBody: bytes
    )
    {
        var client :- expect S3.S3Client();

        var ret := client.GetObject(input);

        expect(ret.Success?);

        // we only care about the Body
        var MyBody := ret.value.Body;
        expect MyBody.Some?;

        var bodyValue :- expect Collect(MyBody.value);
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

        expect(ret.Success?), ret.error;
    }

    method Collect(e: DataStream<uint8, Error>) returns (s: Result<bytes, Error>) 
    {
        var reader := e.Reader();
        var a: BatchSeqWriter := new BatchSeqWriter();
        var aTotalProof := new BatchSeqWriterTotalProof(a);
        reader.ForEach(a, aTotalProof);
        return Success(a.elements);
    }
}
