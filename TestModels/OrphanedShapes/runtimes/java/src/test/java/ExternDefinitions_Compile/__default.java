// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package ExternDefinitions_Compile;

import simple.orphaned.internaldafny.types.*;
import OrphanedResource_Compile.*;
import simple.orphaned.ToDafny;
import simple.orphaned.ToNative;
import Wrappers_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default extends _ExternBase___default {
    public static simple.orphaned.internaldafny.types.OrphanedStructure InitializeOrphanedStructure(simple.orphaned.internaldafny.types.OrphanedStructure input) {
      simple.orphaned.model.OrphanedStructure nativeStructure = ToNative.OrphanedStructure(input);
      simple.orphaned.model.OrphanedStructure newNativeStructure = nativeStructure.toBuilder().stringValue(
        "the extern MUST use Smithy-generated conversions to set this value in the native structure"
      ).build();
      simple.orphaned.internaldafny.types.OrphanedStructure newDafnyStructure = ToDafny.OrphanedStructure(newNativeStructure);
      return newDafnyStructure;
    }

    public static Result<simple.orphaned.internaldafny.types.OrphanedResourceOperationOutput, simple.orphaned.internaldafny.types.Error> CallNativeOrphanedResource(OrphanedResource_Compile.OrphanedResource input) {
      simple.orphaned.IOrphanedResource nativeResource = ToNative.OrphanedResource(input);
      simple.orphaned.model.OrphanedResourceOperationOutput output = nativeResource.OrphanedResourceOperation(
        simple.orphaned.model.OrphanedResourceOperationInput.builder()
          .someString("the extern MUST provide this string to the native resource's operation")
          .build()
      );
      simple.orphaned.internaldafny.types.OrphanedResourceOperationOutput dafnyOutput = ToDafny.OrphanedResourceOperationOutput(output);
      return Result.create_Success(
        simple.orphaned.internaldafny.types.OrphanedResourceOperationOutput._typeDescriptor(),
        simple.orphaned.internaldafny.types.Error._typeDescriptor(),
        dafnyOutput
      );
    }

    public static simple.orphaned.internaldafny.types.Error CallNativeOrphanedError(simple.orphaned.internaldafny.types.Error input) {
      simple.orphaned.model.OrphanedError nativeError = ToNative.Error((simple.orphaned.internaldafny.types.Error_OrphanedError) input);
      simple.orphaned.model.OrphanedError updatedNativeError = nativeError.toBuilder()
        .message("the extern MUST set this string using the catch-all error converter, NOT the orphaned error-specific converter")
        .build();
      simple.orphaned.internaldafny.types.Error dafnyErrorAgain = ToDafny.Error(updatedNativeError);
      return dafnyErrorAgain;
    }
}
