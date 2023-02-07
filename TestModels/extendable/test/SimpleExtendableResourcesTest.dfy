// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module SimpleExtendableResourcesTest {
  import SimpleExtendableResources
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers


  method {:test} TestClient()
  {
    var client :- expect SimpleExtendableResources.SimpleExtendableResources();
  }

  method {:extern "Simple.Extendable.Resources.NativeResource", "DafnyFactory"} DafnyFactory(
  ) returns (
    output: Types.IExtendableResource
  )
    ensures output.ValidState() && fresh(output.History) && fresh(output.Modifies)

  method {:test} TestExternExtendableResource()
  {
    var resource := DafnyFactory();
    var dataInput: Types.GetResourceDataInput := allNone();
    var dataOutput: Types.GetResourceDataOutput :- expect resource.GetResourceData(dataInput);
    checkNone(dataOutput);

    dataInput := allSome();
    dataOutput :- expect resource.GetResourceData(dataInput);
    checkSome(dataOutput);

    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );

    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;

    errorOutput := resource.AlwaysModeledError(errorInput);
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    expect actualError == Types.SimpleExtendableResourcesException(message := "Hard Coded Exception in src/dafny");
  }

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

  method checkNone(
    output: Types.GetResourceDataOutput
  )
  {
    expect Option.None == output.stringValue;
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
    output: Types.GetResourceDataOutput
  )
  {
    expect Option.Some("Some") == output.stringValue;
    expect Option.Some([1]) == output.blobValue;
    expect Option.Some(true) == output.booleanValue;
    expect Option.Some(1) == output.integerValue;
    expect Option.Some(1) == output.longValue; 
  }
}  
