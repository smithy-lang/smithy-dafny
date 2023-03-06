// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module SimpleDoubleTest {
  import SimpleDouble
  import Types = SimpleTypesDoubleTypes
  import Operations = SimpleDoubleOperations
  import opened Wrappers
  import opened StandardLibrary.UInt
  method {:test} GetDouble()
  {
    var client :- expect SimpleDouble.SimpleDouble();
    TestGetDouble(client);
  }
  
  method TestGetDouble(client: Types.ISimpleTypesDoubleClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var s: seq<UInt.uint8> := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7];
    var input := Types.GetDoubleInput(value:= Some(s));
    var output :- expect client.GetDouble(input);
    expect output.value.Some?;
    var isDouble :=  Operations.ValidateDoubleType(output.value.value);
    expect isDouble;
  }
}
