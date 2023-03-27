package Dafny.Simple.Extendable.Resources.Wrapped;

import simple.extendable.resources.SimpleExtendableResources;
import simple.extendable.resources.ToNative;
import simple.extendable.resources.wrapped.TestSimpleExtendableResources;

import Dafny.Simple.Extendable.Resources.Types.ISimpleExtendableResourcesClient;
import Dafny.Simple.Extendable.Resources.Types.Error;

import Dafny.Simple.Extendable.Resources.Types.SimpleExtendableResourcesConfig;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleExtendableResourcesClient, Error> WrappedSimpleExtendableResources(SimpleExtendableResourcesConfig config) {
        simple.extendable.resources.model.SimpleExtendableResourcesConfig wrappedConfig = ToNative.SimpleExtendableResourcesConfig(config);
        simple.extendable.resources.SimpleExtendableResources impl = SimpleExtendableResources.builder().SimpleExtendableResourcesConfig(wrappedConfig).build();
        TestSimpleExtendableResources wrappedClient = TestSimpleExtendableResources.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
