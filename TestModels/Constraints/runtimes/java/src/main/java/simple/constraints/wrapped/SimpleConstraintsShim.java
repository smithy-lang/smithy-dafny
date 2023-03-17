package simple.constraints.wrapped;

import simple.constraints.ToDafny;
import simple.constraints.ToNative;
import simple.constraints.model.OpaqueError;

import Dafny.Simple.Constraints.Types.Error;
import Dafny.Simple.Constraints.Types.GetConstraintsInput;
import Dafny.Simple.Constraints.Types.GetConstraintsOutput;
import Wrappers_Compile.Result;

public class SimpleConstraintsShim implements Dafny.Simple.Constraints.Types.ISimpleConstraintsClient {

    public simple.constraints.SimpleConstraints _impl;

    public SimpleConstraintsShim(simple.constraints.SimpleConstraints impl) {
        this._impl = impl;
    }

    @Override
    public Result<GetConstraintsOutput, Error> GetConstraints(GetConstraintsInput dafnyInput) {
        simple.constraints.model.GetConstraintsInput nativeInput = ToNative.GetConstraintsInput(dafnyInput);
        try {
            simple.constraints.model.GetConstraintsOutput nativeOutput = this._impl.GetConstraints(nativeInput);
            GetConstraintsOutput dafnyOutput = ToDafny.GetConstraintsOutput(nativeOutput);
            return Result.create_Success(dafnyOutput);
        } catch (Exception ex) {
            simple.constraints.model.OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
            return Result.create_Failure(ToDafny.Error(error));
        }
    }
}
