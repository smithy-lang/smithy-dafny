// Class __default
// Dafny class __default compiled into Java
package SimpleConstraintsImpl_Compile;

import simple.constraints.internaldafny.types.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> GetConstraints(Config config, simple.constraints.internaldafny.types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> output = Wrappers_Compile.Result.<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error>Default(simple.constraints.internaldafny.types.GetConstraintsOutput._typeDescriptor(), simple.constraints.internaldafny.types.Error._typeDescriptor(), simple.constraints.internaldafny.types.GetConstraintsOutput.Default());
    simple.constraints.internaldafny.types.GetConstraintsOutput _19_res;
    _19_res = simple.constraints.internaldafny.types.GetConstraintsOutput.create((input).dtor_MyString(), (input).dtor_NonEmptyString(), (input).dtor_StringLessThanOrEqualToTen(), (input).dtor_MyBlob(), (input).dtor_NonEmptyBlob(), (input).dtor_BlobLessThanOrEqualToTen(), (input).dtor_MyList(), (input).dtor_NonEmptyList(), (input).dtor_ListLessThanOrEqualToTen(), (input).dtor_MyMap(), (input).dtor_NonEmptyMap(), (input).dtor_MapLessThanOrEqualToTen(), (input).dtor_OneToTen(), Wrappers_Compile.Option.<java.lang.Long>create_None(simple.constraints.internaldafny.types.TenToTen._typeDescriptor()), (input).dtor_GreaterThanOne(), (input).dtor_LessThanTen(), (input).dtor_MyUtf8Bytes(), (input).dtor_MyListOfUtf8Bytes());
    output = Wrappers_Compile.Result.<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error>create_Success(simple.constraints.internaldafny.types.GetConstraintsOutput._typeDescriptor(), simple.constraints.internaldafny.types.Error._typeDescriptor(), _19_res);
    return output;
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraintsImpl._default";
  }
}
