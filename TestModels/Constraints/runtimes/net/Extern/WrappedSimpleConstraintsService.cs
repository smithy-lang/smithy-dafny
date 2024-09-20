// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Constraints;
using Simple.Constraints.Wrapped;
using TypeConversion = Simple.Constraints.TypeConversion;
namespace simple.constraints.internaldafny.wrapped
{
    public partial class __default
    {
        [System.Obsolete]
        public static _IResult<types.ISimpleConstraintsClient, types._IError> WrappedSimpleConstraints(types._ISimpleConstraintsConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_constraints__S23_SimpleConstraintsConfig(config);
            var impl = new SimpleConstraints(wrappedConfig);
            var wrappedClient = new SimpleConstraintsShim(impl);
            return Result<types.ISimpleConstraintsClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
