package Wrapped;

import simple.constraints.SimpleConstraints;
import simple.constraints.ToNative;
import simple.constraints.wrapped.SimpleConstraintsShim;

import Dafny.Simple.Constraints.Types.Error;
import Dafny.Simple.Constraints.Types.ISimpleConstraintsClient;
import Dafny.Simple.Constraints.Types.SimpleConstraintsConfig;
import Wrappers_Compile.Result;

public class __default extends Dafny.Simple.Constraints.Wrapped._ExternBase___default{
    public static Result<ISimpleConstraintsClient, Error> WrappedSimpleConstraints(SimpleConstraintsConfig config) {
        simple.constraints.model.SimpleConstraintsConfig wrappedConfig = ToNative.SimpleConstraintsConfig(config);
        simple.constraints.SimpleConstraints impl = SimpleConstraints.builder().SimpleConstraintsConfig(wrappedConfig).build();
        SimpleConstraintsShim wrappedClient = new SimpleConstraintsShim(impl);
        return Result.create_Success(wrappedClient);
    }
}
