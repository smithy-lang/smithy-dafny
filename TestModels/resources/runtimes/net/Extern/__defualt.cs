// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Wrappers_Compile;
using Simple.Resources;
using Simple.Resources.Wrapped;
using Dafny.Simple.Resources.Types;
using TypeConversion = Simple.Resources.TypeConversion;
namespace Dafny.Simple.Resources
{
    public partial class __default
    {
      public static
        Wrappers_Compile._IResult<
          SimpleResources_Compile.SimpleResourcesClient, Dafny.Simple.Resources.Types._IError
        > SimpleResources(Dafny.Simple.Resources.Types._ISimpleResourcesConfig config)
      {
        return SimpleResources_Compile.__default.SimpleResources(config);
      }
    }
}

namespace Dafny.Simple.Resources.Wrapped
{
  public partial class __default
  {
    public static _IResult<
        Types.ISimpleResourcesClient, Types._IError
      > WrappedSimpleResources(Types._ISimpleResourcesConfig config)
    {
      var wrappedConfig =
        TypeConversion.FromDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig(
          config);
      var impl = new SimpleResources(wrappedConfig);
      var wrappedClient = new SimpleResourcesShim(impl);
      return Result<
        Types.ISimpleResourcesClient, Types._IError
      >.create_Success(wrappedClient);
    }
  }
}
