package SimpleExternImpl_Compile;

import Wrappers_Compile.Result;
import simple.dafnyextern.ToNative;
import simple.dafnyextern.internaldafny.types.*;
import simple.dafnyextern.internaldafny.types.Error;

public class __default extends _ExternBase___default {

  public static Result<GetExternOutput, Error> GetExtern(Config config, GetExternInput input) {

    GetExternOutput output = GetExternOutput.create(
      input.dtor_blobValue(),
      input.dtor_booleanValue(),
      input.dtor_stringValue(),
      input.dtor_integerValue(),
      input.dtor_longValue()
    );

    return CreateSuccessOfGetExternOutput(output);
  }

  public static Result<ExternMustErrorOutput, Error> ExternMustError(Config config, ExternMustErrorInput input) {

    simple.dafnyextern.model.ExternMustErrorInput putin = ToNative.ExternMustErrorInput(input);
    RuntimeException err = new RuntimeException(putin.value());

    return CreateFailureOfExternMustErrorOutput(Error.create_Opaque(err));
  }
}
