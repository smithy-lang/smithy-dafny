// Class __default
// Dafny class __default compiled into Java
package SimpleConstraintsImplTest_Compile;

import Helpers_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void TestConstraints()
  {
    simple.constraints.internaldafny.SimpleConstraintsClient _23_client;
    Wrappers_Compile.Result<simple.constraints.internaldafny.SimpleConstraintsClient, simple.constraints.internaldafny.types.Error> _24_valueOrError0 = (Wrappers_Compile.Result<simple.constraints.internaldafny.SimpleConstraintsClient, simple.constraints.internaldafny.types.Error>)null;
    Wrappers_Compile.Result<simple.constraints.internaldafny.SimpleConstraintsClient, simple.constraints.internaldafny.types.Error> _out0;
    _out0 = simple.constraints.internaldafny.__default.SimpleConstraints(simple.constraints.internaldafny.__default.DefaultSimpleConstraintsConfig());
    _24_valueOrError0 = _out0;
    if (!(!((_24_valueOrError0).IsFailure(((dafny.TypeDescriptor<simple.constraints.internaldafny.SimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.SimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("test/SimpleConstraintsImplTest.dfy(16,22): " + java.lang.String.valueOf(_24_valueOrError0));
    }
    _23_client = (_24_valueOrError0).Extract(((dafny.TypeDescriptor<simple.constraints.internaldafny.SimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.SimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor());
    __default.TestGetConstraintWithValidInputs(_23_client);
    __default.TestGetConstraintWithInvalidMyString(_23_client);
  }
  public static void TestGetConstraintWithValidInputs(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _25_input;
    _25_input = Helpers_Compile.__default.GetValidInput();
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _26_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out1;
    _out1 = (client).GetConstraints(_25_input);
    _26_ret = _out1;
    if (!((_26_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/SimpleConstraintsImplTest.dfy(28,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithInvalidMyString(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _27_input;
    _27_input = Helpers_Compile.__default.GetValidInput();
    _27_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_27_input, boxed0 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let0_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed0));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let0_0, boxed1 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _28_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed1));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString("this string is too long"))), boxed2 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let1_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed2));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let1_0, boxed3 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _29_dt__update_hMyString_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed3));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_29_dt__update_hMyString_h0, (_28_dt__update__tmp_h0).dtor_NonEmptyString(), (_28_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_28_dt__update__tmp_h0).dtor_MyBlob(), (_28_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_28_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_28_dt__update__tmp_h0).dtor_MyList(), (_28_dt__update__tmp_h0).dtor_NonEmptyList(), (_28_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_28_dt__update__tmp_h0).dtor_MyMap(), (_28_dt__update__tmp_h0).dtor_NonEmptyMap(), (_28_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_28_dt__update__tmp_h0).dtor_OneToTen(), (_28_dt__update__tmp_h0).dtor_myTenToTen(), (_28_dt__update__tmp_h0).dtor_GreaterThanOne(), (_28_dt__update__tmp_h0).dtor_LessThanTen(), (_28_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_28_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _30_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out2;
    _out2 = (client).GetConstraints(_27_input);
    _30_ret = _out2;
    if (!((_30_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/SimpleConstraintsImplTest.dfy(41,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraintsImplTest._default";
  }
}
