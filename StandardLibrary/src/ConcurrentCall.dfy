// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./StandardLibrary.dfy"
include "./UInt.dfy"

/*
  Call a single function many times in many threads

  CallMany(callee : Callee, serialIters : uint32, concurrentIters : uint32)
  This is effectively 

  for i n 0..concurrentIters
     for j in 0..serialIters
       callee(j, i)

  but multi threaded, so really, in `concurrentIters` concurrent threads we execute

     for j in 0..serialIters
       callee(j, i)

  The i and j passed to callee are generally useless, but can be helpful in certain types of debugging.

*/

module {:extern "ConcurrentCall"} ConcurrentCall {
  import opened StandardLibrary
  import opened Wrappers
  import opened StandardLibrary.UInt

  trait {:termination false} Callee {
    ghost var Modifies: set<object>
    predicate ValidState() reads this

    method call(nameonly serialPos : uint32, nameonly concurrentPos : uint32)
      requires ValidState()
      ensures ValidState()
      modifies Modifies
  }

  method {:extern "ConcurrentCall"} ConcurrentCall(nameonly callee : Callee, nameonly serialIters : uint32, nameonly concurrentIters : uint32)


}
