// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module CodegenPatchesImplTest {
    import CodegenPatches
    import StandardLibrary.UInt
    import opened SimpleCodegenpatchesTypes
    import opened Wrappers
    method{:test} TestCodegenPatches(){
        var client :- expect CodegenPatches.CodegenPatches();
        TestGetString(client);
    }

    method TestGetString(client: ICodegenPatchesClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var s: string := "wassup?";
      var convertedStringInput: GetStringInput := CodegenPatches.Types.GetStringInput(value := Some(s));

      var ret := client.GetString(convertedStringInput);

      expect ret.Success?;
    }
}
