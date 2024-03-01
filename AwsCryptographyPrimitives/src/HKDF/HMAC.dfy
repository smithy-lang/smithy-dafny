// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../Model/AwsCryptographyPrimitivesTypes.dfy"
include "../Digest.dfy"

module {:options "-functionSyntax:4"} {:extern "HMAC"} HMAC {
  import opened Wrappers
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes
  import HashDigest = Digest

  class {:extern "HMac"} HMac {

    // These functions are used to model the extern state
    // https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
    ghost function {:extern} GetKey(): seq<uint8> reads this
    ghost function {:extern} GetDigest(): Types.DigestAlgorithm reads this
    ghost function {:extern} GetInputSoFar(): seq<uint8> reads this

    // A build method is used insted of a constructor
    // because in Java creating a `Mac` object
    // can throw because the Java function takes a string.
    // Dafny constructors MUST succeed so this mismatch
    // make a static Build method required.
    static method {:extern} Build(digest: Types.DigestAlgorithm)
      returns (output: Result<HMac, Types.Error>)
      ensures output.Success?
              ==>
                && output.value.GetDigest() == digest
                && output.value.GetInputSoFar() == []
                && fresh(output.value)

    method {:extern "Init"} Init(key: seq<uint8>)
      requires 0 < |key|
      modifies this
      ensures this.GetKey() == key
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetInputSoFar() == []

    method {:extern "BlockUpdate"} Update(input: seq<uint8>)
      requires |this.GetKey()| > 0
      requires |input| < INT32_MAX_LIMIT
      modifies this
      ensures this.GetInputSoFar() == old(this.GetInputSoFar()) + input
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())

    method {:extern "GetResult"} GetResult() returns (s: seq<uint8>)
      requires |this.GetKey()| > 0
      modifies this
      ensures |s| == HashDigest.Length(this.GetDigest())
      ensures this.GetInputSoFar() == []
      ensures this.GetDigest() == old(this.GetDigest())
      ensures this.GetKey() == old(this.GetKey())
      ensures this.HashSignature(old(this.GetInputSoFar()), s)

    ghost predicate {:axiom} HashSignature(message: seq<uint8>, s: seq<uint8>)

    // The next two functions are for the benefit of the extern implementation to call,
    // avoiding direct references to generic datatype constructors
    // since their calling pattern is different between different versions of Dafny
    // (i.e. after 4.2, explicit type descriptors are required).

    static function CreateHMacSuccess(hmac: HMac): Result<HMac, Types.Error> {
      Success(hmac)
    }

    static function CreateHMacFailure(error: Types.Error): Result<HMac, Types.Error> {
      Failure(error)
    }
  }

  // HMAC Digest is safe to make a Dafny function
  // because HMAC MUST return exactly the same otupt for the same input
  function {:extern "Digest"} Digest(input: Types.HMacInput)
    : ( output: Result<seq<uint8>, Types.Error> )
    ensures output.Success? ==> |output.value| == HashDigest.Length(input.digestAlgorithm)

  // The next two functions are for the benefit of the extern implementation to call,
  // avoiding direct references to generic datatype constructors
  // since their calling pattern is different between different versions of Dafny
  // (i.e. after 4.2, explicit type descriptors are required).

  function CreateDigestSuccess(bytes: seq<uint8>): Result<seq<uint8>, Types.Error> {
    Success(bytes)
  }

  function CreateDigestFailure(error: Types.Error): Result<seq<uint8>, Types.Error> {
    Failure(error)
  }
}
