package Dafny.Simple.Dependencies.Wrapped;

import simple.dependencies.SimpleDependencies;
import simple.dependencies.ToNative;
import simple.dependencies.wrapped.TestSimpleDependencies;

import Dafny.Simple.Dependencies.Types.Error;
import Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient;
import Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleDependenciesClient, Error> WrappedSimpleDependencies(SimpleDependenciesConfig config) {
        simple.dependencies.model.SimpleDependenciesConfig wrappedConfig = ToNative.SimpleDependenciesConfig(config);
        simple.dependencies.SimpleDependencies impl = SimpleDependencies.builder().SimpleDependenciesConfig(wrappedConfig).build();
        TestSimpleDependencies wrappedClient = TestSimpleDependencies.builder().impl(impl).build();
        return Result.create_Success(wrappedClient);
    }
}
