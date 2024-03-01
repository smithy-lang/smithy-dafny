// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module Random {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import ExternRandom
  import Types = AwsCryptographyPrimitivesTypes

  method GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.Error>)
    requires 0 <= i
    ensures res.Success? ==> |res.value| == i as int
  {
    var value :- ExternRandom.GenerateBytes(i);

    :- Need(
      |value| == i as int,
      Types.AwsCryptographicPrimitivesError(message := "Incorrect length from ExternRandom.")
    );

    return Success(value);
  }
}

module {:extern "ExternRandom"} ExternRandom {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  method {:extern} GenerateBytes(i: int32) returns (res: Result<seq<uint8>, Types.OpaqueError>)

  // The next two functions are for the benefit of the extern implementation to call,
  // avoiding direct references to generic datatype constructors
  // since their calling pattern is different between different versions of Dafny
  // (i.e. after 4.2, explicit type descriptors are required).

  function method CreateGenerateBytesSuccess(bytes: seq<uint8>): Result<seq<uint8>, Types.Error> {
    Success(bytes)
  }

  function method CreateGenerateBytesFailure(error: Types.Error): Result<seq<uint8>, Types.Error> {
    Failure(error)
  }
}
