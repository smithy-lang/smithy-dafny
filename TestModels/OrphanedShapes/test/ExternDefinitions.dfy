// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleOrphanedTypes.dfy"
include "../src/OrphanedResource.dfy"

module {:extern} ExternDefinitions {

  import opened Wrappers
  import Types = SimpleOrphanedTypes
  import OrphanedResource

  method TestOrphanedStructure ()
  {
    var uninitializedStructure := Types.OrphanedStructure();
    var initializedStructure := InitializeOrphanedStructure(uninitializedStructure);

    expect initializedStructure.stringValue.Some?;
    expect initializedStructure.stringValue.value == "the extern MUST use Smithy-generated conversions to set this value in the native structure";
  }

  method TestOrphanedResource ()
  {
    var resource := new OrphanedResource.OrphanedResource();
    var ret := CallNativeOrphanedResource(resource);

    expect ret.Success?;
    expect ret.value.someString.Some?;
    expect ret.value.someString.value == "correct string";
  }

  method TestOrphanedError ()
  {
    var error := Types.Error.OrphanedError(message := "TBD");
    var out_error := CallNativeOrphanedError(error);

    expect out_error.OrphanedError?;
    expect out_error.message == "the extern MUST set this string using the catch-all error converter, NOT the orphaned error-specific converter";
  }

  // This extern MUST use Smithy-generated type conversions to initialize the input in the native OrphanedStructure.
  // This will ensure that OrphanedStructure and its conversions are generated,
  // even though OrphanedStructure is "orphaned".

  // OrphanedStructure is orphaned because InitializeOrphanedStructure is not a modelled operation.
  // The Smithy model does not know about this operation,
  //   so it doesn't register OrphanedStructure as an operation shape.
  // If this operation were on the Smithy model,
  //   both the operation and OrphanedStructure would no longer be orphaned,
  //   and wouldn't be useful in an "orphaned shapes" TestModel.
  // Putting all usage of the orphaned shape outside the model's knowledge
  //   lets us test orphaned shape model/conversion generation.
  method {:extern} InitializeOrphanedStructure( input: Types.OrphanedStructure )
    returns (output: Types.OrphanedStructure)

  // This extern MUST use Smithy-generated type conversions to call the operation on the native OrphanedResource.
  // This will ensure that OrphanedResource and its conversions are generated,
  // even though OrphanedResource is "orphaned".
  method {:extern} CallNativeOrphanedResource( input: Types.IOrphanedResource )
    returns (output: Result<Types.OrphanedResourceOperationOutput, Types.Error>)

  // This extern MUST use Smithy-generated type conversions to convert the Dafny error to/from native.
  // In particular, the extern MUST use the catch-all/common error handler for this conversion.
  // The extern MUST NOT use some error handler specific to OrphanedError.
  // This will ensure that orphaned errors are handled in the catch-all/common error handler.
  method {:extern} CallNativeOrphanedError( input: Types.Error )
    returns (output: Types.Error )
}