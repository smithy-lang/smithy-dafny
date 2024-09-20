// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Multiplemodels.Dependencyproject;
using Simple.Multiplemodels.Dependencyproject.Wrapped;
using TypeConversion = Simple.Multiplemodels.Dependencyproject.TypeConversion;
namespace simple.multiplemodels.dependencyproject.internaldafny.wrapped
{
    public partial class __default
    {
        [System.Obsolete]
        public static _IResult<types.IDependencyProjectClient, types._IError> WrappedDependencyProject(types._IDependencyProjectConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N14_multiplemodels__N17_dependencyproject__S23_DependencyProjectConfig(config);
            var impl = new DependencyProject(wrappedConfig);
            var wrappedClient = new DependencyProjectShim(impl);
            return Result<types.IDependencyProjectClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
