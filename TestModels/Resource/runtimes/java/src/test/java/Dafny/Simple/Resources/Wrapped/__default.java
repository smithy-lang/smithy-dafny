package Dafny.Simple.Resources.Wrapped;

import simple.resources.SimpleResources;
import simple.resources.ToNative;
import simple.resources.wrapped.TestSimpleResources;

import Dafny.Simple.Resources.Types.Error;
import Dafny.Simple.Resources.Types.ISimpleResourcesClient;
import Dafny.Simple.Resources.Types.SimpleResourcesConfig;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleResourcesClient, Error> WrappedSimpleResources(SimpleResourcesConfig config) {
        simple.resources.model.SimpleResourcesConfig wrappedConfig = ToNative.SimpleResourcesConfig(config);
        simple.resources.SimpleResources impl = SimpleResources.builder().SimpleResourcesConfig(wrappedConfig).build();
        TestSimpleResources wrappedClient = TestSimpleResources.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
