// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Codegenpatches;
using Simple.Codegenpatches.Wrapped;
using TypeConversion = Simple.Codegenpatches.TypeConversion;
namespace simple.codegenpatches.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ICodegenPatchesClient, types._IError> WrappedCodegenPatches(types._ICodegenPatchesConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N14_codegenpatches__S20_CodegenPatchesConfig(config);
            var impl = new CodegenPatches(wrappedConfig);
            var wrappedClient = new CodegenPatchesShim(impl);
            return Result<types.ICodegenPatchesClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
