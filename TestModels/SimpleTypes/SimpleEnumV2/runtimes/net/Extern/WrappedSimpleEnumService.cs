// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.EnumV2;
using Simple.Types.EnumV2.Wrapped;
using TypeConversion = Simple.Types.EnumV2.TypeConversion;
namespace simple.types.enumv2.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleTypesEnumV2Client, types._IError> WrappedSimpleEnumV2(types._ISimpleEnumV2Config config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N6_enumV2__S18_SimpleEnumV2Config(config);
            var impl = new SimpleEnumV2(wrappedConfig);
            var wrappedClient = new SimpleTypesEnumV2Shim(impl);
            return Result<types.ISimpleTypesEnumV2Client, types._IError>.create_Success(wrappedClient);
        }
    }
}
