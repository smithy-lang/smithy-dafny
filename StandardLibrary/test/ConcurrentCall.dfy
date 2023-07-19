// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/ConcurrentCall.dfy"

module TestCallMany {
  import opened StandardLibrary
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened BoundedInts
  import ConcurrentCall


  class MyCallee extends ConcurrentCall.Callee {
    var count : uint32
    constructor()
      ensures ValidState()
    {
      count := 0;
      Modifies := {this};
    }
    predicate ValidState()
      reads this
    {
      this in Modifies
    }

    method call(nameonly serialPos : uint32, nameonly concurrentPos : uint32)
      requires ValidState()
      ensures ValidState()
      modifies Modifies
    {
      if count < UINT32_MAX {
        count := count + 1; // not technically thread safe, but usually works
      }
    }
  }

  method {:test} TestBasic() {
    var c := new MyCallee();
    ConcurrentCall.ConcurrentCall(callee := c, serialIters := 2, concurrentIters := 3);
    expect c.count == 6;
  }

}
