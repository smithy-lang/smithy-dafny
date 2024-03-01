// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"

module {:extern "UUID"} UUID {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt

  function method {:extern "ToByteArray"} ToByteArray(s: string): (res: Result<seq<uint8>, string>)
    ensures res.Success? ==> |res.value| == 16
    ensures res.Success? ==> FromByteArray(res.value).Success? && FromByteArray(res.value).value == s

  function method {:extern "FromByteArray"} FromByteArray(b: seq<uint8>): (res: Result<string, string>)
    requires |b| == 16

  // GenerateUUID MUST be a method because it does not have deterministic output.
  // Even adding `reads *` would not be adequate.
  // This would only map all possible heap states onto a single  `GenerateUUID` call
  // meaning that 2 consecutive calls would still produce the same result
  // because functions MUST NOT mutate the heap.
  method {:extern "GenerateUUID"} GenerateUUID() returns (res: Result<string, string>)
    ensures res.Success? ==> 0 < |res.value|

  // The next four functions are for the benefit of the extern implementation to call,
  // avoiding direct references to generic datatype constructors
  // since their calling pattern is different between different versions of Dafny
  // (i.e. after 4.2, explicit type descriptors are required).

  function method CreateBytesSuccess(bytes: seq<uint8>): Result<seq<uint8>, string> {
    Success(bytes)
  }

  function method CreateBytesFailure(error: string): Result<seq<uint8>, string> {
    Failure(error)
  }

  function method CreateStringSuccess(s: string): Result<string, string> {
    Success(s)
  }

  function method CreateStringFailure(error: string): Result<string, string> {
    Failure(error)
  }
}
