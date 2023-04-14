package Dafny.Simple.Errors.Wrapped;

import simple.errors.SimpleErrors;
import simple.errors.ToNative;
import simple.errors.wrapped.TestSimpleErrors;

import Dafny.Simple.Errors.Types.Error;
import Dafny.Simple.Errors.Types.ISimpleErrorsClient;
import Dafny.Simple.Errors.Types.SimpleErrorsConfig;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleErrorsClient, Error> WrappedSimpleErrors(SimpleErrorsConfig config) {
        simple.errors.model.SimpleErrorsConfig wrappedConfig = ToNative.SimpleErrorsConfig(config);
        simple.errors.SimpleErrors impl = SimpleErrors.builder().SimpleErrorsConfig(wrappedConfig).build();
        TestSimpleErrors wrappedClient = TestSimpleErrors.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
