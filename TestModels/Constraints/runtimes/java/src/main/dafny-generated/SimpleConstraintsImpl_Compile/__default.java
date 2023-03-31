// Class __default
// Dafny class __default compiled into Java
package SimpleConstraintsImpl_Compile;

import Dafny.Simple.Constraints.Types.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> GetConstraints(Config config, Dafny.Simple.Constraints.Types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    Dafny.Simple.Constraints.Types.GetConstraintsOutput _0_res;
    _0_res = Dafny.Simple.Constraints.Types.GetConstraintsOutput.create((input).dtor_MyString(), (input).dtor_NonEmptyString(), (input).dtor_StringLessThanOrEqualToTen(), (input).dtor_MyBlob(), (input).dtor_NonEmptyBlob(), (input).dtor_BlobLessThanOrEqualToTen(), (input).dtor_MyList(), (input).dtor_NonEmptyList(), (input).dtor_ListLessThanOrEqualToTen(), (input).dtor_MyMap(), (input).dtor_NonEmptyMap(), (input).dtor_MapLessThanOrEqualToTen(), (input).dtor_Alphabetic(), (input).dtor_OneToTen(), (input).dtor_GreaterThanOne(), (input).dtor_LessThanTen(), (input).dtor_MyUniqueList(), (input).dtor_MyComplexUniqueList(), (input).dtor_MyUtf8Bytes(), (input).dtor_MyListOfUtf8Bytes());
    output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error>create_Success(_0_res);
    return output;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraintsImpl_Compile._default";
  }
}
