// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using software.amazon.cryptography.standardlibrary.internaldafny.Wrappers;
using simple.constraints.internaldafny.types;
using Simple.Constraints;
using Simple.Constraints.Wrapped;
using TypeConversion = Simple.Constraints.TypeConversion;
namespace WrappedSimpleConstraintsService
{
    public partial class __default
    {
        public static _IResult<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types._IError> WrappedSimpleConstraints(simple.constraints.internaldafny.types._ISimpleConstraintsConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_constraints__S23_SimpleConstraintsConfig(config);
            var impl = new Simple.Constraints.SimpleConstraints(wrappedConfig);
            var wrappedClient = new SimpleConstraintsShim(impl);
            return Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types._IError>.create_Success(wrappedClient);
        }
    }
}
