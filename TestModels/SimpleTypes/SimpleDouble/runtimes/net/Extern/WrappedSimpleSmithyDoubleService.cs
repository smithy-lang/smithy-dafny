// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.SmithyDouble;
using Simple.Types.SmithyDouble.Wrapped;
using TypeConversion = Simple.Types.SmithyDouble.TypeConversion;
namespace simple.types.smithydouble.internaldafny.wrapped
{
  public partial class __default
  {
    public static _IResult<types.ISimpleTypesDoubleClient, types._IError> WrappedSimpleDouble(types._ISimpleDoubleConfig config)
    {
      var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N12_smithyDouble__S18_SimpleDoubleConfig(config);
      var impl = new SimpleDouble(wrappedConfig);
      var wrappedClient = new SimpleTypesDoubleShim(impl);
      return Result<types.ISimpleTypesDoubleClient, types._IError>.create_Success(wrappedClient);
    }
  }
}
