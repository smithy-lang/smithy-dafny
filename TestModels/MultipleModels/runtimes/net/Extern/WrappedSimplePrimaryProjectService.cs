// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Multiplemodels.Primaryproject;
using Simple.Multiplemodels.Primaryproject.Wrapped;
using TypeConversion = Simple.Multiplemodels.Primaryproject.TypeConversion;
namespace simple.multiplemodels.primaryproject.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.IPrimaryProjectClient, types._IError> WrappedPrimaryProject(types._IPrimaryProjectConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N14_multiplemodels__N14_primaryproject__S20_PrimaryProjectConfig(config);
            var impl = new PrimaryProject(wrappedConfig);
            var wrappedClient = new PrimaryProjectShim(impl);
            return Result<types.IPrimaryProjectClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
