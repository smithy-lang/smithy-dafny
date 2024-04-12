// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.SmithyString;
using Simple.Types.SmithyString.Wrapped;
using TypeConversion = Simple.Types.SmithyString.TypeConversion;
namespace simple.types.smithystring.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleTypesStringClient, types._IError> WrappedSimpleString(types._ISimpleStringConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N12_smithyString__S18_SimpleStringConfig(config);
            var impl = new SimpleString(wrappedConfig);
            var wrappedClient = new SimpleTypesStringShim(impl);
            return Result<types.ISimpleTypesStringClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
