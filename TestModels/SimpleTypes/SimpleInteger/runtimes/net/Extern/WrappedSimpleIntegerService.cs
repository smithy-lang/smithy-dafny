// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.Integer;
using Simple.Types.Integer.Wrapped;
using TypeConversion = Simple.Types.Integer.TypeConversion ;
namespace simple.types.integer.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleTypesIntegerClient, types._IError> WrappedSimpleInteger(types._ISimpleIntegerConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N7_integer__S19_SimpleIntegerConfig(config);
            var impl = new SimpleInteger(wrappedConfig);
            var wrappedClient = new SimpleTypesIntegerShim(impl);
            return Result<types.ISimpleTypesIntegerClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
