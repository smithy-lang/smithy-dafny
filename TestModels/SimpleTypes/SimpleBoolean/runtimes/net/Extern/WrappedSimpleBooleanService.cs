// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.Boolean;
using Simple.Types.Boolean.Wrapped;
using TypeConversion = Simple.Types.Boolean.TypeConversion;
namespace simple.types.boolean.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleTypesBooleanClient, types._IError> WrappedSimpleBoolean(types._ISimpleBooleanConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N7_boolean__S19_SimpleBooleanConfig(config);
            var impl = new SimpleBoolean(wrappedConfig);
            var wrappedClient = new SimpleTypesBooleanShim(impl);
            return Result<types.ISimpleTypesBooleanClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
