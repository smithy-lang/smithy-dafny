// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Wrappers_Compile;
using Simple.Extendable.Resources;
using Simple.Extendable.Resources.Wrapped;
using TypeConversion = Simple.Extendable.Resources.TypeConversion;

namespace Dafny.Simple.Extendable.Resources.Wrapped
{
  public partial class __default
  {
    public static _IResult<
      Types.ISimpleExtendableResourcesClient,
      Types._IError
    > WrappedSimpleExtendableResources(
      Types._ISimpleExtendableResourcesConfig config
    )
    {
      var wrappedConfig =
        TypeConversion.FromDafny_N6_simple__N10_extendable__N9_resources__S31_SimpleExtendableResourcesConfig(config);
      var impl = new SimpleExtendableResources(wrappedConfig);
      var wrappedClient = new SimpleExtendableResourcesShim(impl);
      return Result<
        Types.ISimpleExtendableResourcesClient,
        Types._IError
      >.create_Success(wrappedClient);
    }
  }
}

namespace Dafny.Simple.Extendable.Resources.NativeResourceFactory
{
  public partial class __default
  {
    public static Dafny.Simple.Extendable.Resources.Types.IExtendableResource DafnyFactory()
    {
      return TypeConversion.ToDafny_N6_simple__N10_extendable__N9_resources__S27_ExtendableResourceReference(
        NativeResource.NativeFactory());
    }
  }
}
