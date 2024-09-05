// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Constructor;
using Simple.Constructor.Wrapped;
using TypeConversion = Simple.Constructor.TypeConversion;
namespace simple.constructor.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleConstructorClient, types._IError> WrappedSimpleConstructor(types._ISimpleConstructorConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_constructor__S23_SimpleConstructorConfig(config);
            var impl = new SimpleConstructor(wrappedConfig);
            var wrappedClient = new SimpleConstructorShim(impl);
            return Result<types.ISimpleConstructorClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
