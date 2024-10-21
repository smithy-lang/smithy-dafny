// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module Helpers {
  import Types = SimpleResourcesTypes
  import opened Wrappers

  function method allNone(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := None,
      booleanValue := None,
      stringValue := None,
      integerValue := None,
      longValue := None
    )
  }

  method checkMostNone(
    name: string,
    output: Types.GetResourceDataOutput
  )
  {
    expect Some(name) == output.stringValue;
    expect None == output.blobValue;
    expect None == output.booleanValue;
    expect None == output.integerValue;
    expect None == output.longValue; 
  }

  function method allSome(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := Some([1]),
      booleanValue := Some(true),
      stringValue := Some("Some"),
      integerValue := Some(1),
      longValue := Some(1)
    )
  }

  method checkSome(
    name: string,
    output: Types.GetResourceDataOutput
  )
  {
    expect Some(name + " Some") == output.stringValue;
    expect Some([1]) == output.blobValue;
    expect Some(true) == output.booleanValue;
    expect Some(1) == output.integerValue;
    expect Some(1) == output.longValue; 
  }

  function method allMutableNone(): Types.GetMutableResourceDataInput
  {
   Types.GetMutableResourceDataInput(
      blobValue := None,
      booleanValue := None,
      stringValue := None,
      integerValue := None,
      longValue := None
    )
  }

  method checkMutableMostNone(
    name: string,
    output: Types.GetMutableResourceDataOutput
  )
  {
    expect Some(name) == output.stringValue;
    expect None == output.blobValue;
    expect None == output.booleanValue;
    expect None == output.integerValue;
    expect None == output.longValue; 
  }

  function method allMutableSome(): Types.GetMutableResourceDataInput
  {
   Types.GetMutableResourceDataInput(
      blobValue := Some([1]),
      booleanValue := Some(true),
      stringValue := Some("Some"),
      integerValue := Some(1),
      longValue := Some(1)
    )
  }

  method checkMutableSome(
    name: string,
    output: Types.GetMutableResourceDataOutput
  )
  {
    expect Some(name + " Some") == output.stringValue;
    expect Some([1]) == output.blobValue;
    expect Some(true) == output.booleanValue;
    expect Some(1) == output.integerValue;
    expect Some(1) == output.longValue; 
  }
}
