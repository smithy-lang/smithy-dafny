// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using Wrappers_Compile;
using Simple.Extendable.Resources;
using Simple.Extendable.Resources.Wrapped;
using TypeConversion = Simple.Extendable.Resources.TypeConversion;

namespace simple.extendable.resources.internaldafny.wrapped
{
  public partial class __default
  {
    public static _IResult<
      types.ISimpleExtendableResourcesClient,
      types._IError
    > WrappedSimpleExtendableResources(
      types._ISimpleExtendableResourcesConfig config
    )
    {
      var wrappedConfig =
        TypeConversion.FromDafny_N6_simple__N10_extendable__N9_resources__S31_SimpleExtendableResourcesConfig(config);
      var impl = new SimpleExtendableResources(wrappedConfig);
      var wrappedClient = new SimpleExtendableResourcesShim(impl);
      return Result<
        types.ISimpleExtendableResourcesClient,
        types._IError
      >.create_Success(wrappedClient);
    }
  }
}

namespace simple.extendable.resources.internaldafny.nativeresourcefactory
{
  public partial class __default
  {
    public static simple.extendable.resources.internaldafny.types.IExtendableResource DafnyFactory()
    {
      return TypeConversion.ToDafny_N6_simple__N10_extendable__N9_resources__S27_ExtendableResourceReference(
        NativeResource.NativeFactory());
    }
  }
}
