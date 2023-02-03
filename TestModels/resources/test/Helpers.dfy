// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module Helpers {
  import Types = SimpleResourcesTypes
  import opened Wrappers

  function method allNone(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := Option.None(),
      booleanValue := Option.None(),
      stringValue := Option.None(),
      integerValue := Option.None(),
      longValue := Option.None()
    )
  }

  method checkMostNone(
    name: string,
    output: Types.GetResourceDataOutput
  )
    requires |name| > 0
  {
    expect Option.Some(name) == output.stringValue;
    expect Option.None() == output.blobValue;
    expect Option.None() == output.booleanValue;
    expect Option.None() == output.integerValue;
    expect Option.None() == output.longValue; 
  }

  function method allSome(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := Option.Some([1]),
      booleanValue := Option.Some(true),
      stringValue := Option.Some("Some"),
      integerValue := Option.Some(1),
      longValue := Option.Some(1)
    )
  }

  method checkSome(
    name: string,
    output: Types.GetResourceDataOutput
  )
    requires |name| > 0
  {
    expect Option.Some(name + " Some") == output.stringValue;
    expect Option.Some([1]) == output.blobValue;
    expect Option.Some(true) == output.booleanValue;
    expect Option.Some(1) == output.integerValue;
    expect Option.Some(1) == output.longValue; 
  }
}
