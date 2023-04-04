package Dafny.Simple.Extendable.Resources.Wrapped;

import simple.extendable.resources.SimpleExtendableResources;
import simple.extendable.resources.ToNative;
import simple.extendable.resources.wrapped.TestSimpleExtendableResources;

import Dafny.Simple.Extendable.Resources.Types.IExtendableResource;
import Dafny.Simple.Extendable.Resources.Types.ISimpleExtendableResourcesClient;
import Dafny.Simple.Extendable.Resources.Types.Error;

import Dafny.Simple.Extendable.Resources.Types.SimpleExtendableResourcesConfig;
import Simple.Extendable.Resources.NativeResource;
import Wrappers_Compile.Result;

import static Dafny.Simple.Extendable.Resources.NativeResourceFactory.__default.DafnyFactory;

public class __default extends _ExternBase___default {
    public static Result<ISimpleExtendableResourcesClient, Error> WrappedSimpleExtendableResources(SimpleExtendableResourcesConfig config) {
        TestUnwrapExtendable();
        simple.extendable.resources.model.SimpleExtendableResourcesConfig wrappedConfig = ToNative.SimpleExtendableResourcesConfig(config);
        simple.extendable.resources.SimpleExtendableResources impl = SimpleExtendableResources.builder().SimpleExtendableResourcesConfig(wrappedConfig).build();
        TestSimpleExtendableResources wrappedClient = TestSimpleExtendableResources.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }

    /**
     * We cannot call ToNative from Dafny source code. But we need to test this un-wrapping.
     */
    public static void TestUnwrapExtendable() {
        IExtendableResource dafnyWrappingNativeWrappingDafny = DafnyFactory();
        simple.extendable.resources.IExtendableResource nativeWrappingDafny = ToNative.ExtendableResource(dafnyWrappingNativeWrappingDafny);
        if (!(nativeWrappingDafny instanceof NativeResource)) {
            throw new AssertionError(
                    "Polymorph MUST generate conversion methods " +
                            "capable of wrapping & un-wrapping" +
                            "these native resources.");
        }
    }
}
