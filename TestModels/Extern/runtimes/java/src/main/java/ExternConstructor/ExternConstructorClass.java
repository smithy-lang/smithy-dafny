package ExternConstructor;

import Wrappers_Compile.Result;
import dafny.DafnySequence;
import simple.dafnyextern.internaldafny.types.Error;
import software.amazon.smithy.dafny.conversion.ToNative;

public class ExternConstructorClass {

  final private DafnySequence<? extends Character> str;

  public ExternConstructorClass(DafnySequence<? extends Character> input) {
    str = input;
  }

  public static Result<ExternConstructorClass, Error> Build(DafnySequence<? extends Character> input) {
    String inputString = ToNative.Simple.String(input);

    if ("Error".equals(inputString)) {
      RuntimeException err = new RuntimeException("Constructor Exception");
      return _ExternBase___default.CreateFailureOfBuild(Error.create_Opaque(err));
    } else {
      return _ExternBase___default.CreateSuccessOfBuild(new ExternConstructorClass(input));
    }
  }

  public Result<DafnySequence<? extends Character>, Error> GetValue() {
    return _ExternBase___default.CreateSuccessOfGetValue(str);
  }
}
