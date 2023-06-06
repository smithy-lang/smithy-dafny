// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Wrappers_Compile;
using Simple.Resources;
using Simple.Resources.Wrapped;
using simple.resources.internaldafny.types;
using TypeConversion = Simple.Resources.TypeConversion;
// TODO: Not sure what is going on... figure out why we no longer need the SimpleResources method.
/*namespace simple.resources.internaldafny
{
  public partial class __default
  {
    public static
      Wrappers_Compile._IResult<
        SimpleResources_Compile.SimpleResourcesClient, simple.resources.internaldafny.types._IError
      > SimpleResources(simple.resources.internaldafny.types._ISimpleResourcesConfig config)
    {
      return SimpleResources_Compile.__default.SimpleResources(config);
    }
  }
}*/

namespace simple.resources.internaldafny.wrapped
{
  public partial class __default
  {
    public static _IResult<
        types.ISimpleResourcesClient, types._IError
      > WrappedSimpleResources(types._ISimpleResourcesConfig config)
    {
      var wrappedConfig =
        TypeConversion.FromDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig(
          config);
      var impl = new SimpleResources(wrappedConfig);
      var wrappedClient = new SimpleResourcesShim(impl);
      return Result<
        types.ISimpleResourcesClient, types._IError
      >.create_Success(wrappedClient);
    }
  }
}
