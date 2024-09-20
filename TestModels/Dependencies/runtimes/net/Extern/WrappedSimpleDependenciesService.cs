// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Dependencies;
using Simple.Dependencies.Wrapped;
using TypeConversion = Simple.Dependencies.TypeConversion;
namespace simple.dependencies.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleDependenciesClient, types._IError> WrappedSimpleDependencies(types._ISimpleDependenciesConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N12_dependencies__S24_SimpleDependenciesConfig(config);
            var impl = new SimpleDependencies(wrappedConfig);
            var wrappedClient = new SimpleDependenciesShim(impl);
            return Result<types.ISimpleDependenciesClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
