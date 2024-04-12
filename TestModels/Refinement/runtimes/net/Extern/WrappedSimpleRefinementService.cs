// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Refinement;
using Simple.Refinement.Wrapped;
using TypeConversion = Simple.Refinement.TypeConversion;
namespace simple.refinement.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleRefinementClient, types._IError> WrappedSimpleRefinement(types._ISimpleRefinementConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N10_refinement__S22_SimpleRefinementConfig(config);
            var impl = new SimpleRefinement(wrappedConfig);
            var wrappedClient = new SimpleRefinementShim(impl);
            return Result<types.ISimpleRefinementClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
