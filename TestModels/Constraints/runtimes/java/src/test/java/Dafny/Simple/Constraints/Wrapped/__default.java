package Dafny.Simple.Constraints.Wrapped;

import simple.constraints.SimpleConstraints;
import simple.constraints.ToNative;
import simple.constraints.wrapped.SimpleConstraintsShim;

import Dafny.Simple.Constraints.Types.ISimpleConstraintsClient;
import Dafny.Simple.Constraints.Types.SimpleConstraintsConfig;
import Dafny.Simple.Constraints.Types.Error;
import Wrappers_Compile.Result;

public class __default extends _ExternBase___default {
    public static Result<ISimpleConstraintsClient, Error> WrappedSimpleConstraints(SimpleConstraintsConfig config) {
        simple.constraints.model.SimpleConstraintsConfig wrappedConfig = ToNative.SimpleConstraintsConfig(config);
        simple.constraints.SimpleConstraints impl = SimpleConstraints.builder().SimpleConstraintsConfig(wrappedConfig).build();
        SimpleConstraintsShim wrappedClient = new SimpleConstraintsShim(impl);
        return Result.create_Success(wrappedClient);
    }
}
