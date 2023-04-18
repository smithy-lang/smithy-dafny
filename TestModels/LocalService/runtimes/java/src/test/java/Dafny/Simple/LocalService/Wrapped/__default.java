package Dafny.Simple.LocalService.Wrapped;

import simple.localService.SimpleLocalService;
import simple.localService.ToDafny;
import simple.localService.ToNative;
import simple.localService.wrapped.TestSimpleLocalService;

import Dafny.Simple.LocalService.Types.ISimpleLocalServiceClient;
import Dafny.Simple.LocalService.Types.SimpleLocalServiceConfig;
import Dafny.Simple.LocalService.Types.Error;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleLocalServiceClient, Error> WrappedSimpleLocalService(SimpleLocalServiceConfig config) {
        simple.localService.model.SimpleLocalServiceConfig wrappedConfig = ToNative.SimpleLocalServiceConfig(config);
        simple.localService.SimpleLocalService impl = SimpleLocalService.builder().SimpleLocalServiceConfig(wrappedConfig).build();
        TestToNativeAndToDafnyLocalService(impl);
        TestSimpleLocalService wrappedClient = TestSimpleLocalService.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }

    // TODO: Determine how to replace this test with Dafny Source Code
    /**
     * We have not developed the ability to call ToNative from Dafny source code at this time.
     * But we need to test this un-wrapping, so this is written in native code until we figure that out.
     */
    public static void TestToNativeAndToDafnyLocalService(SimpleLocalService nativeValue) {
        Dafny.Simple.LocalService.Types.ISimpleLocalServiceClient dafnyValue = ToDafny.SimpleLocalService(nativeValue);
        //noinspection unused
        simple.localService.SimpleLocalService recreateNativeValue = ToNative.SimpleLocalService(dafnyValue);
    }
}
