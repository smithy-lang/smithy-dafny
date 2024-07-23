// Class __default
// Dafny class __default compiled into Java
package WrappedSimpleConstraintsTest_Compile;

import Helpers_Compile.*;
import SimpleConstraintsImplTest_Compile.*;
import simple.constraints.internaldafny.wrapped.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void TestConstraints()
  {
    simple.constraints.internaldafny.types.ISimpleConstraintsClient _31_client;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error> _32_valueOrError0 = (Wrappers_Compile.Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error>)null;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error> _out3;
    _out3 = simple.constraints.internaldafny.wrapped.__default.WrappedSimpleConstraints(simple.constraints.internaldafny.wrapped.__default.WrappedDefaultSimpleConstraintsConfig());
    _32_valueOrError0 = _out3;
    if (!(!((_32_valueOrError0).IsFailure(((dafny.TypeDescriptor<simple.constraints.internaldafny.types.ISimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.types.ISimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(14,18): " + java.lang.String.valueOf(_32_valueOrError0));
    }
    _31_client = (_32_valueOrError0).Extract(((dafny.TypeDescriptor<simple.constraints.internaldafny.types.ISimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.types.ISimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor());
    __default.TestGetConstraintWithValidInputs(_31_client);
    __default.TestGetConstraintWithMyString(_31_client);
    __default.TestGetConstraintWithOneToTen(_31_client);
    __default.TestGetConstraintWithTenToTen(_31_client);
    __default.TestGetConstraintWithLessThanTen(_31_client);
    __default.TestGetConstraintWithNonEmptyString(_31_client);
    __default.TestGetConstraintWithStringLessThanOrEqualToTen(_31_client);
    __default.TestGetConstraintWithMyBlob(_31_client);
    __default.TestGetConstraintWithNonEmptyBlob(_31_client);
    __default.TestGetConstraintWithBlobLessThanOrEqualToTen(_31_client);
    __default.TestGetConstraintWithMyList(_31_client);
    __default.TestGetConstraintWithNonEmptyList(_31_client);
    __default.TestGetConstraintWithListLessThanOrEqualToTen(_31_client);
    __default.TestGetConstraintWithMyMap(_31_client);
    __default.TestGetConstraintWithNonEmptyMap(_31_client);
    __default.TestGetConstraintWithMapLessThanOrEqualToTen(_31_client);
    __default.TestGetConstraintWithGreaterThanOne(_31_client);
    __default.TestGetConstraintWithUtf8Bytes(_31_client);
    __default.TestGetConstraintWithListOfUtf8Bytes(_31_client);
  }
  public static void TestGetConstraintWithValidInputs(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _33_input;
    _33_input = Helpers_Compile.__default.GetValidInput();
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _34_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out4;
    _out4 = (client).GetConstraints(_33_input);
    _34_ret = _out4;
    if (!((_34_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(43,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithMyString(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _35_input;
    _35_input = Helpers_Compile.__default.GetValidInput();
    _35_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_35_input, boxed4 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let2_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed4));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let2_0, boxed5 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _36_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed5));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString("this string is really way too long"))), boxed6 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let3_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed6));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let3_0, boxed7 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _37_dt__update_hMyString_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed7));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_37_dt__update_hMyString_h0, (_36_dt__update__tmp_h0).dtor_NonEmptyString(), (_36_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_36_dt__update__tmp_h0).dtor_MyBlob(), (_36_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_36_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_36_dt__update__tmp_h0).dtor_MyList(), (_36_dt__update__tmp_h0).dtor_NonEmptyList(), (_36_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_36_dt__update__tmp_h0).dtor_MyMap(), (_36_dt__update__tmp_h0).dtor_NonEmptyMap(), (_36_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_36_dt__update__tmp_h0).dtor_OneToTen(), (_36_dt__update__tmp_h0).dtor_myTenToTen(), (_36_dt__update__tmp_h0).dtor_GreaterThanOne(), (_36_dt__update__tmp_h0).dtor_LessThanTen(), (_36_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_36_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _38_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out5;
    _out5 = (client).GetConstraints(_35_input);
    _38_ret = _out5;
    if (!((_38_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(55,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _35_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_35_input, boxed8 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let4_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed8));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let4_0, boxed9 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _39_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed9));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString("12345678901"))), boxed10 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let5_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed10));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let5_0, boxed11 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _40_dt__update_hMyString_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed11));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_40_dt__update_hMyString_h1, (_39_dt__update__tmp_h1).dtor_NonEmptyString(), (_39_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_39_dt__update__tmp_h1).dtor_MyBlob(), (_39_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_39_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_39_dt__update__tmp_h1).dtor_MyList(), (_39_dt__update__tmp_h1).dtor_NonEmptyList(), (_39_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_39_dt__update__tmp_h1).dtor_MyMap(), (_39_dt__update__tmp_h1).dtor_NonEmptyMap(), (_39_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_39_dt__update__tmp_h1).dtor_OneToTen(), (_39_dt__update__tmp_h1).dtor_myTenToTen(), (_39_dt__update__tmp_h1).dtor_GreaterThanOne(), (_39_dt__update__tmp_h1).dtor_LessThanTen(), (_39_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_39_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out6;
    _out6 = (client).GetConstraints(_35_input);
    _38_ret = _out6;
    if (!((_38_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(59,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _35_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_35_input, boxed12 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let6_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed12));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let6_0, boxed13 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _41_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed13));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString("1234567890"))), boxed14 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let7_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed14));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let7_0, boxed15 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _42_dt__update_hMyString_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed15));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_42_dt__update_hMyString_h2, (_41_dt__update__tmp_h2).dtor_NonEmptyString(), (_41_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_41_dt__update__tmp_h2).dtor_MyBlob(), (_41_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_41_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_41_dt__update__tmp_h2).dtor_MyList(), (_41_dt__update__tmp_h2).dtor_NonEmptyList(), (_41_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_41_dt__update__tmp_h2).dtor_MyMap(), (_41_dt__update__tmp_h2).dtor_NonEmptyMap(), (_41_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_41_dt__update__tmp_h2).dtor_OneToTen(), (_41_dt__update__tmp_h2).dtor_myTenToTen(), (_41_dt__update__tmp_h2).dtor_GreaterThanOne(), (_41_dt__update__tmp_h2).dtor_LessThanTen(), (_41_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_41_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out7;
    _out7 = (client).GetConstraints(_35_input);
    _38_ret = _out7;
    if (!((_38_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(63,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _35_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_35_input, boxed16 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let8_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed16));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let8_0, boxed17 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _43_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed17));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString("1"))), boxed18 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let9_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed18));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let9_0, boxed19 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _44_dt__update_hMyString_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed19));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_44_dt__update_hMyString_h3, (_43_dt__update__tmp_h3).dtor_NonEmptyString(), (_43_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_43_dt__update__tmp_h3).dtor_MyBlob(), (_43_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_43_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_43_dt__update__tmp_h3).dtor_MyList(), (_43_dt__update__tmp_h3).dtor_NonEmptyList(), (_43_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_43_dt__update__tmp_h3).dtor_MyMap(), (_43_dt__update__tmp_h3).dtor_NonEmptyMap(), (_43_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_43_dt__update__tmp_h3).dtor_OneToTen(), (_43_dt__update__tmp_h3).dtor_myTenToTen(), (_43_dt__update__tmp_h3).dtor_GreaterThanOne(), (_43_dt__update__tmp_h3).dtor_LessThanTen(), (_43_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_43_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out8;
    _out8 = (client).GetConstraints(_35_input);
    _38_ret = _out8;
    if (!((_38_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(67,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _35_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_35_input, boxed20 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let10_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed20));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let10_0, boxed21 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _45_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed21));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.MyString._typeDescriptor(), Helpers_Compile.__default.ForceMyString(dafny.DafnySequence.asString(""))), boxed22 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let11_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed22));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let11_0, boxed23 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _46_dt__update_hMyString_h4 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed23));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create(_46_dt__update_hMyString_h4, (_45_dt__update__tmp_h4).dtor_NonEmptyString(), (_45_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_45_dt__update__tmp_h4).dtor_MyBlob(), (_45_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_45_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_45_dt__update__tmp_h4).dtor_MyList(), (_45_dt__update__tmp_h4).dtor_NonEmptyList(), (_45_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_45_dt__update__tmp_h4).dtor_MyMap(), (_45_dt__update__tmp_h4).dtor_NonEmptyMap(), (_45_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_45_dt__update__tmp_h4).dtor_OneToTen(), (_45_dt__update__tmp_h4).dtor_myTenToTen(), (_45_dt__update__tmp_h4).dtor_GreaterThanOne(), (_45_dt__update__tmp_h4).dtor_LessThanTen(), (_45_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_45_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out9;
    _out9 = (client).GetConstraints(_35_input);
    _38_ret = _out9;
    if (!((_38_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(71,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithOneToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _47_input;
    _47_input = Helpers_Compile.__default.GetValidInput();
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed24 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let12_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed24));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let12_0, boxed25 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _48_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed25));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.valueOf(1000L))), boxed26 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let13_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed26));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let13_0, boxed27 -> {
            Wrappers_Compile.Option<java.lang.Integer> _49_dt__update_hOneToTen_h0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed27));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_48_dt__update__tmp_h0).dtor_MyString(), (_48_dt__update__tmp_h0).dtor_NonEmptyString(), (_48_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_48_dt__update__tmp_h0).dtor_MyBlob(), (_48_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_48_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_48_dt__update__tmp_h0).dtor_MyList(), (_48_dt__update__tmp_h0).dtor_NonEmptyList(), (_48_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_48_dt__update__tmp_h0).dtor_MyMap(), (_48_dt__update__tmp_h0).dtor_NonEmptyMap(), (_48_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), _49_dt__update_hOneToTen_h0, (_48_dt__update__tmp_h0).dtor_myTenToTen(), (_48_dt__update__tmp_h0).dtor_GreaterThanOne(), (_48_dt__update__tmp_h0).dtor_LessThanTen(), (_48_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_48_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _50_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out10;
    _out10 = (client).GetConstraints(_47_input);
    _50_ret = _out10;
    if (!((_50_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(83,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed28 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let14_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed28));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let14_0, boxed29 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _51_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed29));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.valueOf(-1000L))), boxed30 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let15_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed30));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let15_0, boxed31 -> {
            Wrappers_Compile.Option<java.lang.Integer> _52_dt__update_hOneToTen_h1 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed31));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_51_dt__update__tmp_h1).dtor_MyString(), (_51_dt__update__tmp_h1).dtor_NonEmptyString(), (_51_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_51_dt__update__tmp_h1).dtor_MyBlob(), (_51_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_51_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_51_dt__update__tmp_h1).dtor_MyList(), (_51_dt__update__tmp_h1).dtor_NonEmptyList(), (_51_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_51_dt__update__tmp_h1).dtor_MyMap(), (_51_dt__update__tmp_h1).dtor_NonEmptyMap(), (_51_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), _52_dt__update_hOneToTen_h1, (_51_dt__update__tmp_h1).dtor_myTenToTen(), (_51_dt__update__tmp_h1).dtor_GreaterThanOne(), (_51_dt__update__tmp_h1).dtor_LessThanTen(), (_51_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_51_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out11;
    _out11 = (client).GetConstraints(_47_input);
    _50_ret = _out11;
    if (!((_50_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(87,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed32 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let16_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed32));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let16_0, boxed33 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _53_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed33));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.ZERO)), boxed34 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let17_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed34));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let17_0, boxed35 -> {
            Wrappers_Compile.Option<java.lang.Integer> _54_dt__update_hOneToTen_h2 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed35));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_53_dt__update__tmp_h2).dtor_MyString(), (_53_dt__update__tmp_h2).dtor_NonEmptyString(), (_53_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_53_dt__update__tmp_h2).dtor_MyBlob(), (_53_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_53_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_53_dt__update__tmp_h2).dtor_MyList(), (_53_dt__update__tmp_h2).dtor_NonEmptyList(), (_53_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_53_dt__update__tmp_h2).dtor_MyMap(), (_53_dt__update__tmp_h2).dtor_NonEmptyMap(), (_53_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), _54_dt__update_hOneToTen_h2, (_53_dt__update__tmp_h2).dtor_myTenToTen(), (_53_dt__update__tmp_h2).dtor_GreaterThanOne(), (_53_dt__update__tmp_h2).dtor_LessThanTen(), (_53_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_53_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out12;
    _out12 = (client).GetConstraints(_47_input);
    _50_ret = _out12;
    if (!((_50_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(91,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed36 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let18_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed36));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let18_0, boxed37 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _55_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed37));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.ONE)), boxed38 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let19_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed38));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let19_0, boxed39 -> {
            Wrappers_Compile.Option<java.lang.Integer> _56_dt__update_hOneToTen_h3 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed39));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_55_dt__update__tmp_h3).dtor_MyString(), (_55_dt__update__tmp_h3).dtor_NonEmptyString(), (_55_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_55_dt__update__tmp_h3).dtor_MyBlob(), (_55_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_55_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_55_dt__update__tmp_h3).dtor_MyList(), (_55_dt__update__tmp_h3).dtor_NonEmptyList(), (_55_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_55_dt__update__tmp_h3).dtor_MyMap(), (_55_dt__update__tmp_h3).dtor_NonEmptyMap(), (_55_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), _56_dt__update_hOneToTen_h3, (_55_dt__update__tmp_h3).dtor_myTenToTen(), (_55_dt__update__tmp_h3).dtor_GreaterThanOne(), (_55_dt__update__tmp_h3).dtor_LessThanTen(), (_55_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_55_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out13;
    _out13 = (client).GetConstraints(_47_input);
    _50_ret = _out13;
    if (!((_50_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(95,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed40 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let20_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed40));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let20_0, boxed41 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _57_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed41));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.valueOf(10L))), boxed42 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let21_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed42));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let21_0, boxed43 -> {
            Wrappers_Compile.Option<java.lang.Integer> _58_dt__update_hOneToTen_h4 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed43));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_57_dt__update__tmp_h4).dtor_MyString(), (_57_dt__update__tmp_h4).dtor_NonEmptyString(), (_57_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_57_dt__update__tmp_h4).dtor_MyBlob(), (_57_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_57_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_57_dt__update__tmp_h4).dtor_MyList(), (_57_dt__update__tmp_h4).dtor_NonEmptyList(), (_57_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_57_dt__update__tmp_h4).dtor_MyMap(), (_57_dt__update__tmp_h4).dtor_NonEmptyMap(), (_57_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), _58_dt__update_hOneToTen_h4, (_57_dt__update__tmp_h4).dtor_myTenToTen(), (_57_dt__update__tmp_h4).dtor_GreaterThanOne(), (_57_dt__update__tmp_h4).dtor_LessThanTen(), (_57_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_57_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out14;
    _out14 = (client).GetConstraints(_47_input);
    _50_ret = _out14;
    if (!((_50_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(99,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _47_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_47_input, boxed44 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let22_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed44));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let22_0, boxed45 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _59_dt__update__tmp_h5 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed45));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.OneToTen._typeDescriptor(), Helpers_Compile.__default.ForceOneToTen(java.math.BigInteger.valueOf(11L))), boxed46 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let23_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed46));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let23_0, boxed47 -> {
            Wrappers_Compile.Option<java.lang.Integer> _60_dt__update_hOneToTen_h5 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed47));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_59_dt__update__tmp_h5).dtor_MyString(), (_59_dt__update__tmp_h5).dtor_NonEmptyString(), (_59_dt__update__tmp_h5).dtor_StringLessThanOrEqualToTen(), (_59_dt__update__tmp_h5).dtor_MyBlob(), (_59_dt__update__tmp_h5).dtor_NonEmptyBlob(), (_59_dt__update__tmp_h5).dtor_BlobLessThanOrEqualToTen(), (_59_dt__update__tmp_h5).dtor_MyList(), (_59_dt__update__tmp_h5).dtor_NonEmptyList(), (_59_dt__update__tmp_h5).dtor_ListLessThanOrEqualToTen(), (_59_dt__update__tmp_h5).dtor_MyMap(), (_59_dt__update__tmp_h5).dtor_NonEmptyMap(), (_59_dt__update__tmp_h5).dtor_MapLessThanOrEqualToTen(), _60_dt__update_hOneToTen_h5, (_59_dt__update__tmp_h5).dtor_myTenToTen(), (_59_dt__update__tmp_h5).dtor_GreaterThanOne(), (_59_dt__update__tmp_h5).dtor_LessThanTen(), (_59_dt__update__tmp_h5).dtor_MyUtf8Bytes(), (_59_dt__update__tmp_h5).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out15;
    _out15 = (client).GetConstraints(_47_input);
    _50_ret = _out15;
    if (!((_50_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(103,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithTenToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _61_input;
    _61_input = Helpers_Compile.__default.GetValidInput();
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed48 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let24_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed48));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let24_0, boxed49 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _62_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed49));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(1000L))), boxed50 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let25_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed50));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let25_0, boxed51 -> {
            Wrappers_Compile.Option<java.lang.Long> _63_dt__update_hmyTenToTen_h0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed51));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_62_dt__update__tmp_h0).dtor_MyString(), (_62_dt__update__tmp_h0).dtor_NonEmptyString(), (_62_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_62_dt__update__tmp_h0).dtor_MyBlob(), (_62_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_62_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_62_dt__update__tmp_h0).dtor_MyList(), (_62_dt__update__tmp_h0).dtor_NonEmptyList(), (_62_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_62_dt__update__tmp_h0).dtor_MyMap(), (_62_dt__update__tmp_h0).dtor_NonEmptyMap(), (_62_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_62_dt__update__tmp_h0).dtor_OneToTen(), _63_dt__update_hmyTenToTen_h0, (_62_dt__update__tmp_h0).dtor_GreaterThanOne(), (_62_dt__update__tmp_h0).dtor_LessThanTen(), (_62_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_62_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _64_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out16;
    _out16 = (client).GetConstraints(_61_input);
    _64_ret = _out16;
    if (!((_64_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(115,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed52 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let26_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed52));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let26_0, boxed53 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _65_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed53));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(-1000L))), boxed54 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let27_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed54));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let27_0, boxed55 -> {
            Wrappers_Compile.Option<java.lang.Long> _66_dt__update_hmyTenToTen_h1 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed55));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_65_dt__update__tmp_h1).dtor_MyString(), (_65_dt__update__tmp_h1).dtor_NonEmptyString(), (_65_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_65_dt__update__tmp_h1).dtor_MyBlob(), (_65_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_65_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_65_dt__update__tmp_h1).dtor_MyList(), (_65_dt__update__tmp_h1).dtor_NonEmptyList(), (_65_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_65_dt__update__tmp_h1).dtor_MyMap(), (_65_dt__update__tmp_h1).dtor_NonEmptyMap(), (_65_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_65_dt__update__tmp_h1).dtor_OneToTen(), _66_dt__update_hmyTenToTen_h1, (_65_dt__update__tmp_h1).dtor_GreaterThanOne(), (_65_dt__update__tmp_h1).dtor_LessThanTen(), (_65_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_65_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out17;
    _out17 = (client).GetConstraints(_61_input);
    _64_ret = _out17;
    if (!((_64_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(119,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed56 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let28_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed56));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let28_0, boxed57 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _67_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed57));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(-11L))), boxed58 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let29_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed58));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let29_0, boxed59 -> {
            Wrappers_Compile.Option<java.lang.Long> _68_dt__update_hmyTenToTen_h2 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed59));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_67_dt__update__tmp_h2).dtor_MyString(), (_67_dt__update__tmp_h2).dtor_NonEmptyString(), (_67_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_67_dt__update__tmp_h2).dtor_MyBlob(), (_67_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_67_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_67_dt__update__tmp_h2).dtor_MyList(), (_67_dt__update__tmp_h2).dtor_NonEmptyList(), (_67_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_67_dt__update__tmp_h2).dtor_MyMap(), (_67_dt__update__tmp_h2).dtor_NonEmptyMap(), (_67_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_67_dt__update__tmp_h2).dtor_OneToTen(), _68_dt__update_hmyTenToTen_h2, (_67_dt__update__tmp_h2).dtor_GreaterThanOne(), (_67_dt__update__tmp_h2).dtor_LessThanTen(), (_67_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_67_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out18;
    _out18 = (client).GetConstraints(_61_input);
    _64_ret = _out18;
    if (!((_64_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(123,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed60 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let30_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed60));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let30_0, boxed61 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _69_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed61));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(-10L))), boxed62 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let31_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed62));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let31_0, boxed63 -> {
            Wrappers_Compile.Option<java.lang.Long> _70_dt__update_hmyTenToTen_h3 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed63));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_69_dt__update__tmp_h3).dtor_MyString(), (_69_dt__update__tmp_h3).dtor_NonEmptyString(), (_69_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_69_dt__update__tmp_h3).dtor_MyBlob(), (_69_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_69_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_69_dt__update__tmp_h3).dtor_MyList(), (_69_dt__update__tmp_h3).dtor_NonEmptyList(), (_69_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_69_dt__update__tmp_h3).dtor_MyMap(), (_69_dt__update__tmp_h3).dtor_NonEmptyMap(), (_69_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_69_dt__update__tmp_h3).dtor_OneToTen(), _70_dt__update_hmyTenToTen_h3, (_69_dt__update__tmp_h3).dtor_GreaterThanOne(), (_69_dt__update__tmp_h3).dtor_LessThanTen(), (_69_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_69_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out19;
    _out19 = (client).GetConstraints(_61_input);
    _64_ret = _out19;
    if (!((_64_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(127,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed64 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let32_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed64));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let32_0, boxed65 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _71_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed65));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.ZERO)), boxed66 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let33_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed66));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let33_0, boxed67 -> {
            Wrappers_Compile.Option<java.lang.Long> _72_dt__update_hmyTenToTen_h4 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed67));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_71_dt__update__tmp_h4).dtor_MyString(), (_71_dt__update__tmp_h4).dtor_NonEmptyString(), (_71_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_71_dt__update__tmp_h4).dtor_MyBlob(), (_71_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_71_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_71_dt__update__tmp_h4).dtor_MyList(), (_71_dt__update__tmp_h4).dtor_NonEmptyList(), (_71_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_71_dt__update__tmp_h4).dtor_MyMap(), (_71_dt__update__tmp_h4).dtor_NonEmptyMap(), (_71_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_71_dt__update__tmp_h4).dtor_OneToTen(), _72_dt__update_hmyTenToTen_h4, (_71_dt__update__tmp_h4).dtor_GreaterThanOne(), (_71_dt__update__tmp_h4).dtor_LessThanTen(), (_71_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_71_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out20;
    _out20 = (client).GetConstraints(_61_input);
    _64_ret = _out20;
    if (!((_64_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(131,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed68 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let34_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed68));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let34_0, boxed69 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _73_dt__update__tmp_h5 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed69));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(10L))), boxed70 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let35_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed70));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let35_0, boxed71 -> {
            Wrappers_Compile.Option<java.lang.Long> _74_dt__update_hmyTenToTen_h5 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed71));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_73_dt__update__tmp_h5).dtor_MyString(), (_73_dt__update__tmp_h5).dtor_NonEmptyString(), (_73_dt__update__tmp_h5).dtor_StringLessThanOrEqualToTen(), (_73_dt__update__tmp_h5).dtor_MyBlob(), (_73_dt__update__tmp_h5).dtor_NonEmptyBlob(), (_73_dt__update__tmp_h5).dtor_BlobLessThanOrEqualToTen(), (_73_dt__update__tmp_h5).dtor_MyList(), (_73_dt__update__tmp_h5).dtor_NonEmptyList(), (_73_dt__update__tmp_h5).dtor_ListLessThanOrEqualToTen(), (_73_dt__update__tmp_h5).dtor_MyMap(), (_73_dt__update__tmp_h5).dtor_NonEmptyMap(), (_73_dt__update__tmp_h5).dtor_MapLessThanOrEqualToTen(), (_73_dt__update__tmp_h5).dtor_OneToTen(), _74_dt__update_hmyTenToTen_h5, (_73_dt__update__tmp_h5).dtor_GreaterThanOne(), (_73_dt__update__tmp_h5).dtor_LessThanTen(), (_73_dt__update__tmp_h5).dtor_MyUtf8Bytes(), (_73_dt__update__tmp_h5).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out21;
    _out21 = (client).GetConstraints(_61_input);
    _64_ret = _out21;
    if (!((_64_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(135,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _61_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_61_input, boxed72 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let36_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed72));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let36_0, boxed73 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _75_dt__update__tmp_h6 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed73));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Long>create_Some(simple.constraints.internaldafny.types.TenToTen._typeDescriptor(), Helpers_Compile.__default.ForceTenToTen(java.math.BigInteger.valueOf(11L))), boxed74 -> {
          Wrappers_Compile.Option<java.lang.Long> _pat_let37_0 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed74));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Long>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let37_0, boxed75 -> {
            Wrappers_Compile.Option<java.lang.Long> _76_dt__update_hmyTenToTen_h6 = ((Wrappers_Compile.Option<java.lang.Long>)(java.lang.Object)(boxed75));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_75_dt__update__tmp_h6).dtor_MyString(), (_75_dt__update__tmp_h6).dtor_NonEmptyString(), (_75_dt__update__tmp_h6).dtor_StringLessThanOrEqualToTen(), (_75_dt__update__tmp_h6).dtor_MyBlob(), (_75_dt__update__tmp_h6).dtor_NonEmptyBlob(), (_75_dt__update__tmp_h6).dtor_BlobLessThanOrEqualToTen(), (_75_dt__update__tmp_h6).dtor_MyList(), (_75_dt__update__tmp_h6).dtor_NonEmptyList(), (_75_dt__update__tmp_h6).dtor_ListLessThanOrEqualToTen(), (_75_dt__update__tmp_h6).dtor_MyMap(), (_75_dt__update__tmp_h6).dtor_NonEmptyMap(), (_75_dt__update__tmp_h6).dtor_MapLessThanOrEqualToTen(), (_75_dt__update__tmp_h6).dtor_OneToTen(), _76_dt__update_hmyTenToTen_h6, (_75_dt__update__tmp_h6).dtor_GreaterThanOne(), (_75_dt__update__tmp_h6).dtor_LessThanTen(), (_75_dt__update__tmp_h6).dtor_MyUtf8Bytes(), (_75_dt__update__tmp_h6).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out22;
    _out22 = (client).GetConstraints(_61_input);
    _64_ret = _out22;
    if (!((_64_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(139,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithLessThanTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _77_input;
    _77_input = Helpers_Compile.__default.GetValidInput();
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed76 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let38_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed76));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let38_0, boxed77 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _78_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed77));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.valueOf(1000L))), boxed78 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let39_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed78));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let39_0, boxed79 -> {
            Wrappers_Compile.Option<java.lang.Integer> _79_dt__update_hLessThanTen_h0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed79));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_78_dt__update__tmp_h0).dtor_MyString(), (_78_dt__update__tmp_h0).dtor_NonEmptyString(), (_78_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_78_dt__update__tmp_h0).dtor_MyBlob(), (_78_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_78_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_78_dt__update__tmp_h0).dtor_MyList(), (_78_dt__update__tmp_h0).dtor_NonEmptyList(), (_78_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_78_dt__update__tmp_h0).dtor_MyMap(), (_78_dt__update__tmp_h0).dtor_NonEmptyMap(), (_78_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_78_dt__update__tmp_h0).dtor_OneToTen(), (_78_dt__update__tmp_h0).dtor_myTenToTen(), (_78_dt__update__tmp_h0).dtor_GreaterThanOne(), _79_dt__update_hLessThanTen_h0, (_78_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_78_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _80_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out23;
    _out23 = (client).GetConstraints(_77_input);
    _80_ret = _out23;
    if (!((_80_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(151,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed80 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let40_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed80));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let40_0, boxed81 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _81_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed81));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.valueOf(-1000L))), boxed82 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let41_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed82));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let41_0, boxed83 -> {
            Wrappers_Compile.Option<java.lang.Integer> _82_dt__update_hLessThanTen_h1 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed83));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_81_dt__update__tmp_h1).dtor_MyString(), (_81_dt__update__tmp_h1).dtor_NonEmptyString(), (_81_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_81_dt__update__tmp_h1).dtor_MyBlob(), (_81_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_81_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_81_dt__update__tmp_h1).dtor_MyList(), (_81_dt__update__tmp_h1).dtor_NonEmptyList(), (_81_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_81_dt__update__tmp_h1).dtor_MyMap(), (_81_dt__update__tmp_h1).dtor_NonEmptyMap(), (_81_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_81_dt__update__tmp_h1).dtor_OneToTen(), (_81_dt__update__tmp_h1).dtor_myTenToTen(), (_81_dt__update__tmp_h1).dtor_GreaterThanOne(), _82_dt__update_hLessThanTen_h1, (_81_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_81_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out24;
    _out24 = (client).GetConstraints(_77_input);
    _80_ret = _out24;
    if (!((_80_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(155,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed84 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let42_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed84));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let42_0, boxed85 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _83_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed85));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.ZERO)), boxed86 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let43_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed86));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let43_0, boxed87 -> {
            Wrappers_Compile.Option<java.lang.Integer> _84_dt__update_hLessThanTen_h2 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed87));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_83_dt__update__tmp_h2).dtor_MyString(), (_83_dt__update__tmp_h2).dtor_NonEmptyString(), (_83_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_83_dt__update__tmp_h2).dtor_MyBlob(), (_83_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_83_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_83_dt__update__tmp_h2).dtor_MyList(), (_83_dt__update__tmp_h2).dtor_NonEmptyList(), (_83_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_83_dt__update__tmp_h2).dtor_MyMap(), (_83_dt__update__tmp_h2).dtor_NonEmptyMap(), (_83_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_83_dt__update__tmp_h2).dtor_OneToTen(), (_83_dt__update__tmp_h2).dtor_myTenToTen(), (_83_dt__update__tmp_h2).dtor_GreaterThanOne(), _84_dt__update_hLessThanTen_h2, (_83_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_83_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out25;
    _out25 = (client).GetConstraints(_77_input);
    _80_ret = _out25;
    if (!((_80_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(159,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed88 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let44_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed88));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let44_0, boxed89 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _85_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed89));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.ONE)), boxed90 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let45_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed90));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let45_0, boxed91 -> {
            Wrappers_Compile.Option<java.lang.Integer> _86_dt__update_hLessThanTen_h3 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed91));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_85_dt__update__tmp_h3).dtor_MyString(), (_85_dt__update__tmp_h3).dtor_NonEmptyString(), (_85_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_85_dt__update__tmp_h3).dtor_MyBlob(), (_85_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_85_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_85_dt__update__tmp_h3).dtor_MyList(), (_85_dt__update__tmp_h3).dtor_NonEmptyList(), (_85_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_85_dt__update__tmp_h3).dtor_MyMap(), (_85_dt__update__tmp_h3).dtor_NonEmptyMap(), (_85_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_85_dt__update__tmp_h3).dtor_OneToTen(), (_85_dt__update__tmp_h3).dtor_myTenToTen(), (_85_dt__update__tmp_h3).dtor_GreaterThanOne(), _86_dt__update_hLessThanTen_h3, (_85_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_85_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out26;
    _out26 = (client).GetConstraints(_77_input);
    _80_ret = _out26;
    if (!((_80_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(163,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed92 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let46_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed92));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let46_0, boxed93 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _87_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed93));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.valueOf(10L))), boxed94 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let47_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed94));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let47_0, boxed95 -> {
            Wrappers_Compile.Option<java.lang.Integer> _88_dt__update_hLessThanTen_h4 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed95));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_87_dt__update__tmp_h4).dtor_MyString(), (_87_dt__update__tmp_h4).dtor_NonEmptyString(), (_87_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_87_dt__update__tmp_h4).dtor_MyBlob(), (_87_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_87_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_87_dt__update__tmp_h4).dtor_MyList(), (_87_dt__update__tmp_h4).dtor_NonEmptyList(), (_87_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_87_dt__update__tmp_h4).dtor_MyMap(), (_87_dt__update__tmp_h4).dtor_NonEmptyMap(), (_87_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_87_dt__update__tmp_h4).dtor_OneToTen(), (_87_dt__update__tmp_h4).dtor_myTenToTen(), (_87_dt__update__tmp_h4).dtor_GreaterThanOne(), _88_dt__update_hLessThanTen_h4, (_87_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_87_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out27;
    _out27 = (client).GetConstraints(_77_input);
    _80_ret = _out27;
    if (!((_80_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(167,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _77_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_77_input, boxed96 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let48_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed96));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let48_0, boxed97 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _89_dt__update__tmp_h5 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed97));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.LessThanTen._typeDescriptor(), Helpers_Compile.__default.ForceLessThanTen(java.math.BigInteger.valueOf(11L))), boxed98 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let49_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed98));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let49_0, boxed99 -> {
            Wrappers_Compile.Option<java.lang.Integer> _90_dt__update_hLessThanTen_h5 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed99));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_89_dt__update__tmp_h5).dtor_MyString(), (_89_dt__update__tmp_h5).dtor_NonEmptyString(), (_89_dt__update__tmp_h5).dtor_StringLessThanOrEqualToTen(), (_89_dt__update__tmp_h5).dtor_MyBlob(), (_89_dt__update__tmp_h5).dtor_NonEmptyBlob(), (_89_dt__update__tmp_h5).dtor_BlobLessThanOrEqualToTen(), (_89_dt__update__tmp_h5).dtor_MyList(), (_89_dt__update__tmp_h5).dtor_NonEmptyList(), (_89_dt__update__tmp_h5).dtor_ListLessThanOrEqualToTen(), (_89_dt__update__tmp_h5).dtor_MyMap(), (_89_dt__update__tmp_h5).dtor_NonEmptyMap(), (_89_dt__update__tmp_h5).dtor_MapLessThanOrEqualToTen(), (_89_dt__update__tmp_h5).dtor_OneToTen(), (_89_dt__update__tmp_h5).dtor_myTenToTen(), (_89_dt__update__tmp_h5).dtor_GreaterThanOne(), _90_dt__update_hLessThanTen_h5, (_89_dt__update__tmp_h5).dtor_MyUtf8Bytes(), (_89_dt__update__tmp_h5).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out28;
    _out28 = (client).GetConstraints(_77_input);
    _80_ret = _out28;
    if (!((_80_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(171,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithNonEmptyString(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _91_input;
    _91_input = Helpers_Compile.__default.GetValidInput();
    _91_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_91_input, boxed100 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let50_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed100));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let50_0, boxed101 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _92_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed101));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.NonEmptyString._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyString(dafny.DafnySequence.asString("this string is really way too long"))), boxed102 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let51_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed102));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let51_0, boxed103 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _93_dt__update_hNonEmptyString_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed103));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_92_dt__update__tmp_h0).dtor_MyString(), _93_dt__update_hNonEmptyString_h0, (_92_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_92_dt__update__tmp_h0).dtor_MyBlob(), (_92_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_92_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_92_dt__update__tmp_h0).dtor_MyList(), (_92_dt__update__tmp_h0).dtor_NonEmptyList(), (_92_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_92_dt__update__tmp_h0).dtor_MyMap(), (_92_dt__update__tmp_h0).dtor_NonEmptyMap(), (_92_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_92_dt__update__tmp_h0).dtor_OneToTen(), (_92_dt__update__tmp_h0).dtor_myTenToTen(), (_92_dt__update__tmp_h0).dtor_GreaterThanOne(), (_92_dt__update__tmp_h0).dtor_LessThanTen(), (_92_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_92_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _94_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out29;
    _out29 = (client).GetConstraints(_91_input);
    _94_ret = _out29;
    if (!((_94_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(183,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _91_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_91_input, boxed104 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let52_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed104));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let52_0, boxed105 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _95_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed105));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.NonEmptyString._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyString(dafny.DafnySequence.asString("12345678901"))), boxed106 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let53_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed106));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let53_0, boxed107 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _96_dt__update_hNonEmptyString_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed107));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_95_dt__update__tmp_h1).dtor_MyString(), _96_dt__update_hNonEmptyString_h1, (_95_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_95_dt__update__tmp_h1).dtor_MyBlob(), (_95_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_95_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_95_dt__update__tmp_h1).dtor_MyList(), (_95_dt__update__tmp_h1).dtor_NonEmptyList(), (_95_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_95_dt__update__tmp_h1).dtor_MyMap(), (_95_dt__update__tmp_h1).dtor_NonEmptyMap(), (_95_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_95_dt__update__tmp_h1).dtor_OneToTen(), (_95_dt__update__tmp_h1).dtor_myTenToTen(), (_95_dt__update__tmp_h1).dtor_GreaterThanOne(), (_95_dt__update__tmp_h1).dtor_LessThanTen(), (_95_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_95_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out30;
    _out30 = (client).GetConstraints(_91_input);
    _94_ret = _out30;
    if (!((_94_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(187,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _91_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_91_input, boxed108 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let54_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed108));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let54_0, boxed109 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _97_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed109));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.NonEmptyString._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyString(dafny.DafnySequence.asString("1234567890"))), boxed110 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let55_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed110));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let55_0, boxed111 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _98_dt__update_hNonEmptyString_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed111));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_97_dt__update__tmp_h2).dtor_MyString(), _98_dt__update_hNonEmptyString_h2, (_97_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_97_dt__update__tmp_h2).dtor_MyBlob(), (_97_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_97_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_97_dt__update__tmp_h2).dtor_MyList(), (_97_dt__update__tmp_h2).dtor_NonEmptyList(), (_97_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_97_dt__update__tmp_h2).dtor_MyMap(), (_97_dt__update__tmp_h2).dtor_NonEmptyMap(), (_97_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_97_dt__update__tmp_h2).dtor_OneToTen(), (_97_dt__update__tmp_h2).dtor_myTenToTen(), (_97_dt__update__tmp_h2).dtor_GreaterThanOne(), (_97_dt__update__tmp_h2).dtor_LessThanTen(), (_97_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_97_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out31;
    _out31 = (client).GetConstraints(_91_input);
    _94_ret = _out31;
    if (!((_94_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(191,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _91_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_91_input, boxed112 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let56_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed112));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let56_0, boxed113 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _99_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed113));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.NonEmptyString._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyString(dafny.DafnySequence.asString("1"))), boxed114 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let57_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed114));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let57_0, boxed115 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _100_dt__update_hNonEmptyString_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed115));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_99_dt__update__tmp_h3).dtor_MyString(), _100_dt__update_hNonEmptyString_h3, (_99_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_99_dt__update__tmp_h3).dtor_MyBlob(), (_99_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_99_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_99_dt__update__tmp_h3).dtor_MyList(), (_99_dt__update__tmp_h3).dtor_NonEmptyList(), (_99_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_99_dt__update__tmp_h3).dtor_MyMap(), (_99_dt__update__tmp_h3).dtor_NonEmptyMap(), (_99_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_99_dt__update__tmp_h3).dtor_OneToTen(), (_99_dt__update__tmp_h3).dtor_myTenToTen(), (_99_dt__update__tmp_h3).dtor_GreaterThanOne(), (_99_dt__update__tmp_h3).dtor_LessThanTen(), (_99_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_99_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out32;
    _out32 = (client).GetConstraints(_91_input);
    _94_ret = _out32;
    if (!((_94_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(195,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _91_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_91_input, boxed116 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let58_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed116));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let58_0, boxed117 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _101_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed117));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.NonEmptyString._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyString(dafny.DafnySequence.asString(""))), boxed118 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let59_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed118));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let59_0, boxed119 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _102_dt__update_hNonEmptyString_h4 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed119));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_101_dt__update__tmp_h4).dtor_MyString(), _102_dt__update_hNonEmptyString_h4, (_101_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_101_dt__update__tmp_h4).dtor_MyBlob(), (_101_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_101_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_101_dt__update__tmp_h4).dtor_MyList(), (_101_dt__update__tmp_h4).dtor_NonEmptyList(), (_101_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_101_dt__update__tmp_h4).dtor_MyMap(), (_101_dt__update__tmp_h4).dtor_NonEmptyMap(), (_101_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_101_dt__update__tmp_h4).dtor_OneToTen(), (_101_dt__update__tmp_h4).dtor_myTenToTen(), (_101_dt__update__tmp_h4).dtor_GreaterThanOne(), (_101_dt__update__tmp_h4).dtor_LessThanTen(), (_101_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_101_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out33;
    _out33 = (client).GetConstraints(_91_input);
    _94_ret = _out33;
    if (!((_94_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(199,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithStringLessThanOrEqualToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _103_input;
    _103_input = Helpers_Compile.__default.GetValidInput();
    _103_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_103_input, boxed120 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let60_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed120));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let60_0, boxed121 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _104_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed121));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.StringLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceStringLessThanOrEqualToTen(dafny.DafnySequence.asString("this string is really way too long"))), boxed122 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let61_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed122));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let61_0, boxed123 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _105_dt__update_hStringLessThanOrEqualToTen_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed123));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_104_dt__update__tmp_h0).dtor_MyString(), (_104_dt__update__tmp_h0).dtor_NonEmptyString(), _105_dt__update_hStringLessThanOrEqualToTen_h0, (_104_dt__update__tmp_h0).dtor_MyBlob(), (_104_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_104_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_104_dt__update__tmp_h0).dtor_MyList(), (_104_dt__update__tmp_h0).dtor_NonEmptyList(), (_104_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_104_dt__update__tmp_h0).dtor_MyMap(), (_104_dt__update__tmp_h0).dtor_NonEmptyMap(), (_104_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_104_dt__update__tmp_h0).dtor_OneToTen(), (_104_dt__update__tmp_h0).dtor_myTenToTen(), (_104_dt__update__tmp_h0).dtor_GreaterThanOne(), (_104_dt__update__tmp_h0).dtor_LessThanTen(), (_104_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_104_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _106_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out34;
    _out34 = (client).GetConstraints(_103_input);
    _106_ret = _out34;
    if (!((_106_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(211,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _103_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_103_input, boxed124 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let62_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed124));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let62_0, boxed125 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _107_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed125));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.StringLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceStringLessThanOrEqualToTen(dafny.DafnySequence.asString("12345678901"))), boxed126 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let63_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed126));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let63_0, boxed127 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _108_dt__update_hStringLessThanOrEqualToTen_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed127));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_107_dt__update__tmp_h1).dtor_MyString(), (_107_dt__update__tmp_h1).dtor_NonEmptyString(), _108_dt__update_hStringLessThanOrEqualToTen_h1, (_107_dt__update__tmp_h1).dtor_MyBlob(), (_107_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_107_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_107_dt__update__tmp_h1).dtor_MyList(), (_107_dt__update__tmp_h1).dtor_NonEmptyList(), (_107_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_107_dt__update__tmp_h1).dtor_MyMap(), (_107_dt__update__tmp_h1).dtor_NonEmptyMap(), (_107_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_107_dt__update__tmp_h1).dtor_OneToTen(), (_107_dt__update__tmp_h1).dtor_myTenToTen(), (_107_dt__update__tmp_h1).dtor_GreaterThanOne(), (_107_dt__update__tmp_h1).dtor_LessThanTen(), (_107_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_107_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out35;
    _out35 = (client).GetConstraints(_103_input);
    _106_ret = _out35;
    if (!((_106_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(215,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _103_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_103_input, boxed128 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let64_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed128));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let64_0, boxed129 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _109_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed129));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.StringLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceStringLessThanOrEqualToTen(dafny.DafnySequence.asString("1234567890"))), boxed130 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let65_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed130));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let65_0, boxed131 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _110_dt__update_hStringLessThanOrEqualToTen_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed131));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_109_dt__update__tmp_h2).dtor_MyString(), (_109_dt__update__tmp_h2).dtor_NonEmptyString(), _110_dt__update_hStringLessThanOrEqualToTen_h2, (_109_dt__update__tmp_h2).dtor_MyBlob(), (_109_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_109_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_109_dt__update__tmp_h2).dtor_MyList(), (_109_dt__update__tmp_h2).dtor_NonEmptyList(), (_109_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_109_dt__update__tmp_h2).dtor_MyMap(), (_109_dt__update__tmp_h2).dtor_NonEmptyMap(), (_109_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_109_dt__update__tmp_h2).dtor_OneToTen(), (_109_dt__update__tmp_h2).dtor_myTenToTen(), (_109_dt__update__tmp_h2).dtor_GreaterThanOne(), (_109_dt__update__tmp_h2).dtor_LessThanTen(), (_109_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_109_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out36;
    _out36 = (client).GetConstraints(_103_input);
    _106_ret = _out36;
    if (!((_106_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(219,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _103_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_103_input, boxed132 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let66_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed132));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let66_0, boxed133 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _111_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed133));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.StringLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceStringLessThanOrEqualToTen(dafny.DafnySequence.asString("1"))), boxed134 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let67_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed134));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let67_0, boxed135 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _112_dt__update_hStringLessThanOrEqualToTen_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed135));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_111_dt__update__tmp_h3).dtor_MyString(), (_111_dt__update__tmp_h3).dtor_NonEmptyString(), _112_dt__update_hStringLessThanOrEqualToTen_h3, (_111_dt__update__tmp_h3).dtor_MyBlob(), (_111_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_111_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_111_dt__update__tmp_h3).dtor_MyList(), (_111_dt__update__tmp_h3).dtor_NonEmptyList(), (_111_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_111_dt__update__tmp_h3).dtor_MyMap(), (_111_dt__update__tmp_h3).dtor_NonEmptyMap(), (_111_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_111_dt__update__tmp_h3).dtor_OneToTen(), (_111_dt__update__tmp_h3).dtor_myTenToTen(), (_111_dt__update__tmp_h3).dtor_GreaterThanOne(), (_111_dt__update__tmp_h3).dtor_LessThanTen(), (_111_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_111_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out37;
    _out37 = (client).GetConstraints(_103_input);
    _106_ret = _out37;
    if (!((_106_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(223,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _103_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_103_input, boxed136 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let68_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed136));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let68_0, boxed137 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _113_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed137));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(simple.constraints.internaldafny.types.StringLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceStringLessThanOrEqualToTen(dafny.DafnySequence.asString(""))), boxed138 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _pat_let69_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed138));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let69_0, boxed139 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _114_dt__update_hStringLessThanOrEqualToTen_h4 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>>)(java.lang.Object)(boxed139));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_113_dt__update__tmp_h4).dtor_MyString(), (_113_dt__update__tmp_h4).dtor_NonEmptyString(), _114_dt__update_hStringLessThanOrEqualToTen_h4, (_113_dt__update__tmp_h4).dtor_MyBlob(), (_113_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_113_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_113_dt__update__tmp_h4).dtor_MyList(), (_113_dt__update__tmp_h4).dtor_NonEmptyList(), (_113_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_113_dt__update__tmp_h4).dtor_MyMap(), (_113_dt__update__tmp_h4).dtor_NonEmptyMap(), (_113_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_113_dt__update__tmp_h4).dtor_OneToTen(), (_113_dt__update__tmp_h4).dtor_myTenToTen(), (_113_dt__update__tmp_h4).dtor_GreaterThanOne(), (_113_dt__update__tmp_h4).dtor_LessThanTen(), (_113_dt__update__tmp_h4).dtor_MyUtf8Bytes(), (_113_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out38;
    _out38 = (client).GetConstraints(_103_input);
    _106_ret = _out38;
    if (!((_106_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(227,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithMyBlob(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _115_input;
    _115_input = Helpers_Compile.__default.GetValidInput();
    _115_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_115_input, boxed140 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let70_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed140));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let70_0, boxed141 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _116_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed141));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.MyBlob._typeDescriptor(), Helpers_Compile.__default.ForceMyBlob(dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor()))), boxed142 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let71_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed142));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let71_0, boxed143 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _117_dt__update_hMyBlob_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed143));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_116_dt__update__tmp_h0).dtor_MyString(), (_116_dt__update__tmp_h0).dtor_NonEmptyString(), (_116_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), _117_dt__update_hMyBlob_h0, (_116_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_116_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_116_dt__update__tmp_h0).dtor_MyList(), (_116_dt__update__tmp_h0).dtor_NonEmptyList(), (_116_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_116_dt__update__tmp_h0).dtor_MyMap(), (_116_dt__update__tmp_h0).dtor_NonEmptyMap(), (_116_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_116_dt__update__tmp_h0).dtor_OneToTen(), (_116_dt__update__tmp_h0).dtor_myTenToTen(), (_116_dt__update__tmp_h0).dtor_GreaterThanOne(), (_116_dt__update__tmp_h0).dtor_LessThanTen(), (_116_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_116_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _118_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out39;
    _out39 = (client).GetConstraints(_115_input);
    _118_ret = _out39;
    if (!((_118_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(239,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _115_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_115_input, boxed144 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let72_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed144));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let72_0, boxed145 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _119_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed145));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.MyBlob._typeDescriptor(), Helpers_Compile.__default.ForceMyBlob(dafny.DafnySequence.<java.lang.Byte> of((byte) 1))), boxed146 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let73_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed146));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let73_0, boxed147 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _120_dt__update_hMyBlob_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed147));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_119_dt__update__tmp_h1).dtor_MyString(), (_119_dt__update__tmp_h1).dtor_NonEmptyString(), (_119_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), _120_dt__update_hMyBlob_h1, (_119_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_119_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_119_dt__update__tmp_h1).dtor_MyList(), (_119_dt__update__tmp_h1).dtor_NonEmptyList(), (_119_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_119_dt__update__tmp_h1).dtor_MyMap(), (_119_dt__update__tmp_h1).dtor_NonEmptyMap(), (_119_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_119_dt__update__tmp_h1).dtor_OneToTen(), (_119_dt__update__tmp_h1).dtor_myTenToTen(), (_119_dt__update__tmp_h1).dtor_GreaterThanOne(), (_119_dt__update__tmp_h1).dtor_LessThanTen(), (_119_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_119_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out40;
    _out40 = (client).GetConstraints(_115_input);
    _118_ret = _out40;
    if (!((_118_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(243,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _115_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_115_input, boxed148 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let74_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed148));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let74_0, boxed149 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _121_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed149));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.MyBlob._typeDescriptor(), Helpers_Compile.__default.ForceMyBlob(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0))), boxed150 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let75_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed150));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let75_0, boxed151 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _122_dt__update_hMyBlob_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed151));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_121_dt__update__tmp_h2).dtor_MyString(), (_121_dt__update__tmp_h2).dtor_NonEmptyString(), (_121_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), _122_dt__update_hMyBlob_h2, (_121_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_121_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_121_dt__update__tmp_h2).dtor_MyList(), (_121_dt__update__tmp_h2).dtor_NonEmptyList(), (_121_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_121_dt__update__tmp_h2).dtor_MyMap(), (_121_dt__update__tmp_h2).dtor_NonEmptyMap(), (_121_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_121_dt__update__tmp_h2).dtor_OneToTen(), (_121_dt__update__tmp_h2).dtor_myTenToTen(), (_121_dt__update__tmp_h2).dtor_GreaterThanOne(), (_121_dt__update__tmp_h2).dtor_LessThanTen(), (_121_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_121_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out41;
    _out41 = (client).GetConstraints(_115_input);
    _118_ret = _out41;
    if (!((_118_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(247,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _115_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_115_input, boxed152 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let76_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed152));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let76_0, boxed153 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _123_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed153));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.MyBlob._typeDescriptor(), Helpers_Compile.__default.ForceMyBlob(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0, (byte) 1))), boxed154 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let77_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed154));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let77_0, boxed155 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _124_dt__update_hMyBlob_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed155));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_123_dt__update__tmp_h3).dtor_MyString(), (_123_dt__update__tmp_h3).dtor_NonEmptyString(), (_123_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), _124_dt__update_hMyBlob_h3, (_123_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_123_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_123_dt__update__tmp_h3).dtor_MyList(), (_123_dt__update__tmp_h3).dtor_NonEmptyList(), (_123_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_123_dt__update__tmp_h3).dtor_MyMap(), (_123_dt__update__tmp_h3).dtor_NonEmptyMap(), (_123_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_123_dt__update__tmp_h3).dtor_OneToTen(), (_123_dt__update__tmp_h3).dtor_myTenToTen(), (_123_dt__update__tmp_h3).dtor_GreaterThanOne(), (_123_dt__update__tmp_h3).dtor_LessThanTen(), (_123_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_123_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out42;
    _out42 = (client).GetConstraints(_115_input);
    _118_ret = _out42;
    if (!((_118_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(251,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithNonEmptyBlob(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _125_input;
    _125_input = Helpers_Compile.__default.GetValidInput();
    _125_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_125_input, boxed156 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let78_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed156));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let78_0, boxed157 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _126_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed157));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.NonEmptyBlob._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyBlob(dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor()))), boxed158 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let79_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed158));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let79_0, boxed159 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _127_dt__update_hNonEmptyBlob_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed159));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_126_dt__update__tmp_h0).dtor_MyString(), (_126_dt__update__tmp_h0).dtor_NonEmptyString(), (_126_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_126_dt__update__tmp_h0).dtor_MyBlob(), _127_dt__update_hNonEmptyBlob_h0, (_126_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_126_dt__update__tmp_h0).dtor_MyList(), (_126_dt__update__tmp_h0).dtor_NonEmptyList(), (_126_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_126_dt__update__tmp_h0).dtor_MyMap(), (_126_dt__update__tmp_h0).dtor_NonEmptyMap(), (_126_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_126_dt__update__tmp_h0).dtor_OneToTen(), (_126_dt__update__tmp_h0).dtor_myTenToTen(), (_126_dt__update__tmp_h0).dtor_GreaterThanOne(), (_126_dt__update__tmp_h0).dtor_LessThanTen(), (_126_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_126_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _128_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out43;
    _out43 = (client).GetConstraints(_125_input);
    _128_ret = _out43;
    if (!((_128_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(263,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _125_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_125_input, boxed160 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let80_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed160));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let80_0, boxed161 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _129_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed161));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.NonEmptyBlob._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyBlob(dafny.DafnySequence.<java.lang.Byte> of((byte) 1))), boxed162 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let81_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed162));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let81_0, boxed163 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _130_dt__update_hNonEmptyBlob_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed163));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_129_dt__update__tmp_h1).dtor_MyString(), (_129_dt__update__tmp_h1).dtor_NonEmptyString(), (_129_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_129_dt__update__tmp_h1).dtor_MyBlob(), _130_dt__update_hNonEmptyBlob_h1, (_129_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_129_dt__update__tmp_h1).dtor_MyList(), (_129_dt__update__tmp_h1).dtor_NonEmptyList(), (_129_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_129_dt__update__tmp_h1).dtor_MyMap(), (_129_dt__update__tmp_h1).dtor_NonEmptyMap(), (_129_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_129_dt__update__tmp_h1).dtor_OneToTen(), (_129_dt__update__tmp_h1).dtor_myTenToTen(), (_129_dt__update__tmp_h1).dtor_GreaterThanOne(), (_129_dt__update__tmp_h1).dtor_LessThanTen(), (_129_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_129_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out44;
    _out44 = (client).GetConstraints(_125_input);
    _128_ret = _out44;
    if (!((_128_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(267,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _125_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_125_input, boxed164 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let82_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed164));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let82_0, boxed165 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _131_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed165));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.NonEmptyBlob._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyBlob(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0))), boxed166 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let83_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed166));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let83_0, boxed167 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _132_dt__update_hNonEmptyBlob_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed167));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_131_dt__update__tmp_h2).dtor_MyString(), (_131_dt__update__tmp_h2).dtor_NonEmptyString(), (_131_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_131_dt__update__tmp_h2).dtor_MyBlob(), _132_dt__update_hNonEmptyBlob_h2, (_131_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_131_dt__update__tmp_h2).dtor_MyList(), (_131_dt__update__tmp_h2).dtor_NonEmptyList(), (_131_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_131_dt__update__tmp_h2).dtor_MyMap(), (_131_dt__update__tmp_h2).dtor_NonEmptyMap(), (_131_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_131_dt__update__tmp_h2).dtor_OneToTen(), (_131_dt__update__tmp_h2).dtor_myTenToTen(), (_131_dt__update__tmp_h2).dtor_GreaterThanOne(), (_131_dt__update__tmp_h2).dtor_LessThanTen(), (_131_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_131_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out45;
    _out45 = (client).GetConstraints(_125_input);
    _128_ret = _out45;
    if (!((_128_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(271,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithBlobLessThanOrEqualToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _133_input;
    _133_input = Helpers_Compile.__default.GetValidInput();
    _133_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_133_input, boxed168 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let84_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed168));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let84_0, boxed169 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _134_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed169));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.BlobLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceBlobLessThanOrEqualToTen(dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor()))), boxed170 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let85_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed170));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let85_0, boxed171 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _135_dt__update_hBlobLessThanOrEqualToTen_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed171));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_134_dt__update__tmp_h0).dtor_MyString(), (_134_dt__update__tmp_h0).dtor_NonEmptyString(), (_134_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_134_dt__update__tmp_h0).dtor_MyBlob(), (_134_dt__update__tmp_h0).dtor_NonEmptyBlob(), _135_dt__update_hBlobLessThanOrEqualToTen_h0, (_134_dt__update__tmp_h0).dtor_MyList(), (_134_dt__update__tmp_h0).dtor_NonEmptyList(), (_134_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_134_dt__update__tmp_h0).dtor_MyMap(), (_134_dt__update__tmp_h0).dtor_NonEmptyMap(), (_134_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_134_dt__update__tmp_h0).dtor_OneToTen(), (_134_dt__update__tmp_h0).dtor_myTenToTen(), (_134_dt__update__tmp_h0).dtor_GreaterThanOne(), (_134_dt__update__tmp_h0).dtor_LessThanTen(), (_134_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_134_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _136_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out46;
    _out46 = (client).GetConstraints(_133_input);
    _136_ret = _out46;
    if (!((_136_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(283,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _133_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_133_input, boxed172 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let86_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed172));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let86_0, boxed173 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _137_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed173));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.BlobLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceBlobLessThanOrEqualToTen(dafny.DafnySequence.<java.lang.Byte> of((byte) 1))), boxed174 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let87_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed174));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let87_0, boxed175 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _138_dt__update_hBlobLessThanOrEqualToTen_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed175));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_137_dt__update__tmp_h1).dtor_MyString(), (_137_dt__update__tmp_h1).dtor_NonEmptyString(), (_137_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_137_dt__update__tmp_h1).dtor_MyBlob(), (_137_dt__update__tmp_h1).dtor_NonEmptyBlob(), _138_dt__update_hBlobLessThanOrEqualToTen_h1, (_137_dt__update__tmp_h1).dtor_MyList(), (_137_dt__update__tmp_h1).dtor_NonEmptyList(), (_137_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_137_dt__update__tmp_h1).dtor_MyMap(), (_137_dt__update__tmp_h1).dtor_NonEmptyMap(), (_137_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_137_dt__update__tmp_h1).dtor_OneToTen(), (_137_dt__update__tmp_h1).dtor_myTenToTen(), (_137_dt__update__tmp_h1).dtor_GreaterThanOne(), (_137_dt__update__tmp_h1).dtor_LessThanTen(), (_137_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_137_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out47;
    _out47 = (client).GetConstraints(_133_input);
    _136_ret = _out47;
    if (!((_136_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(287,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _133_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_133_input, boxed176 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let88_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed176));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let88_0, boxed177 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _139_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed177));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.BlobLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceBlobLessThanOrEqualToTen(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0))), boxed178 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let89_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed178));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let89_0, boxed179 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _140_dt__update_hBlobLessThanOrEqualToTen_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed179));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_139_dt__update__tmp_h2).dtor_MyString(), (_139_dt__update__tmp_h2).dtor_NonEmptyString(), (_139_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_139_dt__update__tmp_h2).dtor_MyBlob(), (_139_dt__update__tmp_h2).dtor_NonEmptyBlob(), _140_dt__update_hBlobLessThanOrEqualToTen_h2, (_139_dt__update__tmp_h2).dtor_MyList(), (_139_dt__update__tmp_h2).dtor_NonEmptyList(), (_139_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_139_dt__update__tmp_h2).dtor_MyMap(), (_139_dt__update__tmp_h2).dtor_NonEmptyMap(), (_139_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_139_dt__update__tmp_h2).dtor_OneToTen(), (_139_dt__update__tmp_h2).dtor_myTenToTen(), (_139_dt__update__tmp_h2).dtor_GreaterThanOne(), (_139_dt__update__tmp_h2).dtor_LessThanTen(), (_139_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_139_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out48;
    _out48 = (client).GetConstraints(_133_input);
    _136_ret = _out48;
    if (!((_136_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(291,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _133_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_133_input, boxed180 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let90_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed180));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let90_0, boxed181 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _141_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed181));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.BlobLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceBlobLessThanOrEqualToTen(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0, (byte) 1))), boxed182 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let91_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed182));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let91_0, boxed183 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _142_dt__update_hBlobLessThanOrEqualToTen_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed183));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_141_dt__update__tmp_h3).dtor_MyString(), (_141_dt__update__tmp_h3).dtor_NonEmptyString(), (_141_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_141_dt__update__tmp_h3).dtor_MyBlob(), (_141_dt__update__tmp_h3).dtor_NonEmptyBlob(), _142_dt__update_hBlobLessThanOrEqualToTen_h3, (_141_dt__update__tmp_h3).dtor_MyList(), (_141_dt__update__tmp_h3).dtor_NonEmptyList(), (_141_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_141_dt__update__tmp_h3).dtor_MyMap(), (_141_dt__update__tmp_h3).dtor_NonEmptyMap(), (_141_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_141_dt__update__tmp_h3).dtor_OneToTen(), (_141_dt__update__tmp_h3).dtor_myTenToTen(), (_141_dt__update__tmp_h3).dtor_GreaterThanOne(), (_141_dt__update__tmp_h3).dtor_LessThanTen(), (_141_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_141_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out49;
    _out49 = (client).GetConstraints(_133_input);
    _136_ret = _out49;
    if (!((_136_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(295,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithMyList(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _143_input;
    _143_input = Helpers_Compile.__default.GetValidInput();
    _143_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_143_input, boxed184 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let92_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed184));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let92_0, boxed185 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _144_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed185));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyList._typeDescriptor(), Helpers_Compile.__default.ForceMyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> empty(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR)))), boxed186 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let93_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed186));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let93_0, boxed187 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _145_dt__update_hMyList_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed187));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_144_dt__update__tmp_h0).dtor_MyString(), (_144_dt__update__tmp_h0).dtor_NonEmptyString(), (_144_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_144_dt__update__tmp_h0).dtor_MyBlob(), (_144_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_144_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), _145_dt__update_hMyList_h0, (_144_dt__update__tmp_h0).dtor_NonEmptyList(), (_144_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_144_dt__update__tmp_h0).dtor_MyMap(), (_144_dt__update__tmp_h0).dtor_NonEmptyMap(), (_144_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_144_dt__update__tmp_h0).dtor_OneToTen(), (_144_dt__update__tmp_h0).dtor_myTenToTen(), (_144_dt__update__tmp_h0).dtor_GreaterThanOne(), (_144_dt__update__tmp_h0).dtor_LessThanTen(), (_144_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_144_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _146_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out50;
    _out50 = (client).GetConstraints(_143_input);
    _146_ret = _out50;
    if (!((_146_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(307,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _143_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_143_input, boxed188 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let94_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed188));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let94_0, boxed189 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _147_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed189));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyList._typeDescriptor(), Helpers_Compile.__default.ForceMyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1")))), boxed190 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let95_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed190));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let95_0, boxed191 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _148_dt__update_hMyList_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed191));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_147_dt__update__tmp_h1).dtor_MyString(), (_147_dt__update__tmp_h1).dtor_NonEmptyString(), (_147_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_147_dt__update__tmp_h1).dtor_MyBlob(), (_147_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_147_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), _148_dt__update_hMyList_h1, (_147_dt__update__tmp_h1).dtor_NonEmptyList(), (_147_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_147_dt__update__tmp_h1).dtor_MyMap(), (_147_dt__update__tmp_h1).dtor_NonEmptyMap(), (_147_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_147_dt__update__tmp_h1).dtor_OneToTen(), (_147_dt__update__tmp_h1).dtor_myTenToTen(), (_147_dt__update__tmp_h1).dtor_GreaterThanOne(), (_147_dt__update__tmp_h1).dtor_LessThanTen(), (_147_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_147_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out51;
    _out51 = (client).GetConstraints(_143_input);
    _146_ret = _out51;
    if (!((_146_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(311,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _143_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_143_input, boxed192 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let96_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed192));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let96_0, boxed193 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _149_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed193));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyList._typeDescriptor(), Helpers_Compile.__default.ForceMyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0")))), boxed194 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let97_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed194));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let97_0, boxed195 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _150_dt__update_hMyList_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed195));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_149_dt__update__tmp_h2).dtor_MyString(), (_149_dt__update__tmp_h2).dtor_NonEmptyString(), (_149_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_149_dt__update__tmp_h2).dtor_MyBlob(), (_149_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_149_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), _150_dt__update_hMyList_h2, (_149_dt__update__tmp_h2).dtor_NonEmptyList(), (_149_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_149_dt__update__tmp_h2).dtor_MyMap(), (_149_dt__update__tmp_h2).dtor_NonEmptyMap(), (_149_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_149_dt__update__tmp_h2).dtor_OneToTen(), (_149_dt__update__tmp_h2).dtor_myTenToTen(), (_149_dt__update__tmp_h2).dtor_GreaterThanOne(), (_149_dt__update__tmp_h2).dtor_LessThanTen(), (_149_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_149_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out52;
    _out52 = (client).GetConstraints(_143_input);
    _146_ret = _out52;
    if (!((_146_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(315,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _143_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_143_input, boxed196 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let98_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed196));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let98_0, boxed197 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _151_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed197));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyList._typeDescriptor(), Helpers_Compile.__default.ForceMyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a")))), boxed198 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let99_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed198));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let99_0, boxed199 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _152_dt__update_hMyList_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed199));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_151_dt__update__tmp_h3).dtor_MyString(), (_151_dt__update__tmp_h3).dtor_NonEmptyString(), (_151_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_151_dt__update__tmp_h3).dtor_MyBlob(), (_151_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_151_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), _152_dt__update_hMyList_h3, (_151_dt__update__tmp_h3).dtor_NonEmptyList(), (_151_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_151_dt__update__tmp_h3).dtor_MyMap(), (_151_dt__update__tmp_h3).dtor_NonEmptyMap(), (_151_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_151_dt__update__tmp_h3).dtor_OneToTen(), (_151_dt__update__tmp_h3).dtor_myTenToTen(), (_151_dt__update__tmp_h3).dtor_GreaterThanOne(), (_151_dt__update__tmp_h3).dtor_LessThanTen(), (_151_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_151_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out53;
    _out53 = (client).GetConstraints(_143_input);
    _146_ret = _out53;
    if (!((_146_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(319,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithNonEmptyList(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _153_input;
    _153_input = Helpers_Compile.__default.GetValidInput();
    _153_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_153_input, boxed200 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let100_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed200));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let100_0, boxed201 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _154_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed201));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyList._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> empty(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR)))), boxed202 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let101_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed202));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let101_0, boxed203 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _155_dt__update_hNonEmptyList_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed203));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_154_dt__update__tmp_h0).dtor_MyString(), (_154_dt__update__tmp_h0).dtor_NonEmptyString(), (_154_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_154_dt__update__tmp_h0).dtor_MyBlob(), (_154_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_154_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_154_dt__update__tmp_h0).dtor_MyList(), _155_dt__update_hNonEmptyList_h0, (_154_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_154_dt__update__tmp_h0).dtor_MyMap(), (_154_dt__update__tmp_h0).dtor_NonEmptyMap(), (_154_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_154_dt__update__tmp_h0).dtor_OneToTen(), (_154_dt__update__tmp_h0).dtor_myTenToTen(), (_154_dt__update__tmp_h0).dtor_GreaterThanOne(), (_154_dt__update__tmp_h0).dtor_LessThanTen(), (_154_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_154_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _156_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out54;
    _out54 = (client).GetConstraints(_153_input);
    _156_ret = _out54;
    if (!((_156_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(331,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _153_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_153_input, boxed204 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let102_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed204));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let102_0, boxed205 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _157_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed205));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyList._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1")))), boxed206 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let103_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed206));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let103_0, boxed207 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _158_dt__update_hNonEmptyList_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed207));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_157_dt__update__tmp_h1).dtor_MyString(), (_157_dt__update__tmp_h1).dtor_NonEmptyString(), (_157_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_157_dt__update__tmp_h1).dtor_MyBlob(), (_157_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_157_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_157_dt__update__tmp_h1).dtor_MyList(), _158_dt__update_hNonEmptyList_h1, (_157_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_157_dt__update__tmp_h1).dtor_MyMap(), (_157_dt__update__tmp_h1).dtor_NonEmptyMap(), (_157_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_157_dt__update__tmp_h1).dtor_OneToTen(), (_157_dt__update__tmp_h1).dtor_myTenToTen(), (_157_dt__update__tmp_h1).dtor_GreaterThanOne(), (_157_dt__update__tmp_h1).dtor_LessThanTen(), (_157_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_157_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out55;
    _out55 = (client).GetConstraints(_153_input);
    _156_ret = _out55;
    if (!((_156_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(335,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _153_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_153_input, boxed208 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let104_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed208));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let104_0, boxed209 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _159_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed209));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyList._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("MoreThentenChar")))), boxed210 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let105_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed210));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let105_0, boxed211 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _160_dt__update_hNonEmptyList_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed211));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_159_dt__update__tmp_h2).dtor_MyString(), (_159_dt__update__tmp_h2).dtor_NonEmptyString(), (_159_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_159_dt__update__tmp_h2).dtor_MyBlob(), (_159_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_159_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_159_dt__update__tmp_h2).dtor_MyList(), _160_dt__update_hNonEmptyList_h2, (_159_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_159_dt__update__tmp_h2).dtor_MyMap(), (_159_dt__update__tmp_h2).dtor_NonEmptyMap(), (_159_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_159_dt__update__tmp_h2).dtor_OneToTen(), (_159_dt__update__tmp_h2).dtor_myTenToTen(), (_159_dt__update__tmp_h2).dtor_GreaterThanOne(), (_159_dt__update__tmp_h2).dtor_LessThanTen(), (_159_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_159_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out56;
    _out56 = (client).GetConstraints(_153_input);
    _156_ret = _out56;
    if (!((_156_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(339,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _153_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_153_input, boxed212 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let106_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed212));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let106_0, boxed213 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _161_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed213));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyList._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyList(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a"), dafny.DafnySequence.asString("MoreThentenChar")))), boxed214 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let107_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed214));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let107_0, boxed215 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _162_dt__update_hNonEmptyList_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed215));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_161_dt__update__tmp_h3).dtor_MyString(), (_161_dt__update__tmp_h3).dtor_NonEmptyString(), (_161_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_161_dt__update__tmp_h3).dtor_MyBlob(), (_161_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_161_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_161_dt__update__tmp_h3).dtor_MyList(), _162_dt__update_hNonEmptyList_h3, (_161_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_161_dt__update__tmp_h3).dtor_MyMap(), (_161_dt__update__tmp_h3).dtor_NonEmptyMap(), (_161_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_161_dt__update__tmp_h3).dtor_OneToTen(), (_161_dt__update__tmp_h3).dtor_myTenToTen(), (_161_dt__update__tmp_h3).dtor_GreaterThanOne(), (_161_dt__update__tmp_h3).dtor_LessThanTen(), (_161_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_161_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out57;
    _out57 = (client).GetConstraints(_153_input);
    _156_ret = _out57;
    if (!((_156_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(343,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithListLessThanOrEqualToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _163_input;
    _163_input = Helpers_Compile.__default.GetValidInput();
    _163_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_163_input, boxed216 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let108_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed216));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let108_0, boxed217 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _164_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed217));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.ListLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceListLessThanOrEqualToTen(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> empty(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR)))), boxed218 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let109_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed218));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let109_0, boxed219 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _165_dt__update_hListLessThanOrEqualToTen_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed219));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_164_dt__update__tmp_h0).dtor_MyString(), (_164_dt__update__tmp_h0).dtor_NonEmptyString(), (_164_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_164_dt__update__tmp_h0).dtor_MyBlob(), (_164_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_164_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_164_dt__update__tmp_h0).dtor_MyList(), (_164_dt__update__tmp_h0).dtor_NonEmptyList(), _165_dt__update_hListLessThanOrEqualToTen_h0, (_164_dt__update__tmp_h0).dtor_MyMap(), (_164_dt__update__tmp_h0).dtor_NonEmptyMap(), (_164_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_164_dt__update__tmp_h0).dtor_OneToTen(), (_164_dt__update__tmp_h0).dtor_myTenToTen(), (_164_dt__update__tmp_h0).dtor_GreaterThanOne(), (_164_dt__update__tmp_h0).dtor_LessThanTen(), (_164_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_164_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _166_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out58;
    _out58 = (client).GetConstraints(_163_input);
    _166_ret = _out58;
    if (!((_166_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(355,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _163_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_163_input, boxed220 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let110_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed220));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let110_0, boxed221 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _167_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed221));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.ListLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceListLessThanOrEqualToTen(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1")))), boxed222 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let111_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed222));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let111_0, boxed223 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _168_dt__update_hListLessThanOrEqualToTen_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed223));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_167_dt__update__tmp_h1).dtor_MyString(), (_167_dt__update__tmp_h1).dtor_NonEmptyString(), (_167_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_167_dt__update__tmp_h1).dtor_MyBlob(), (_167_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_167_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_167_dt__update__tmp_h1).dtor_MyList(), (_167_dt__update__tmp_h1).dtor_NonEmptyList(), _168_dt__update_hListLessThanOrEqualToTen_h1, (_167_dt__update__tmp_h1).dtor_MyMap(), (_167_dt__update__tmp_h1).dtor_NonEmptyMap(), (_167_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_167_dt__update__tmp_h1).dtor_OneToTen(), (_167_dt__update__tmp_h1).dtor_myTenToTen(), (_167_dt__update__tmp_h1).dtor_GreaterThanOne(), (_167_dt__update__tmp_h1).dtor_LessThanTen(), (_167_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_167_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out59;
    _out59 = (client).GetConstraints(_163_input);
    _166_ret = _out59;
    if (!((_166_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(359,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _163_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_163_input, boxed224 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let112_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed224));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let112_0, boxed225 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _169_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed225));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.ListLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceListLessThanOrEqualToTen(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0")))), boxed226 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let113_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed226));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let113_0, boxed227 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _170_dt__update_hListLessThanOrEqualToTen_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed227));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_169_dt__update__tmp_h2).dtor_MyString(), (_169_dt__update__tmp_h2).dtor_NonEmptyString(), (_169_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_169_dt__update__tmp_h2).dtor_MyBlob(), (_169_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_169_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_169_dt__update__tmp_h2).dtor_MyList(), (_169_dt__update__tmp_h2).dtor_NonEmptyList(), _170_dt__update_hListLessThanOrEqualToTen_h2, (_169_dt__update__tmp_h2).dtor_MyMap(), (_169_dt__update__tmp_h2).dtor_NonEmptyMap(), (_169_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_169_dt__update__tmp_h2).dtor_OneToTen(), (_169_dt__update__tmp_h2).dtor_myTenToTen(), (_169_dt__update__tmp_h2).dtor_GreaterThanOne(), (_169_dt__update__tmp_h2).dtor_LessThanTen(), (_169_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_169_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out60;
    _out60 = (client).GetConstraints(_163_input);
    _166_ret = _out60;
    if (!((_166_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(363,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _163_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_163_input, boxed228 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let114_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed228));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let114_0, boxed229 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _171_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed229));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.ListLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceListLessThanOrEqualToTen(dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a")))), boxed230 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _pat_let115_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed230));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let115_0, boxed231 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _172_dt__update_hListLessThanOrEqualToTen_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed231));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_171_dt__update__tmp_h3).dtor_MyString(), (_171_dt__update__tmp_h3).dtor_NonEmptyString(), (_171_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_171_dt__update__tmp_h3).dtor_MyBlob(), (_171_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_171_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_171_dt__update__tmp_h3).dtor_MyList(), (_171_dt__update__tmp_h3).dtor_NonEmptyList(), _172_dt__update_hListLessThanOrEqualToTen_h3, (_171_dt__update__tmp_h3).dtor_MyMap(), (_171_dt__update__tmp_h3).dtor_NonEmptyMap(), (_171_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_171_dt__update__tmp_h3).dtor_OneToTen(), (_171_dt__update__tmp_h3).dtor_myTenToTen(), (_171_dt__update__tmp_h3).dtor_GreaterThanOne(), (_171_dt__update__tmp_h3).dtor_LessThanTen(), (_171_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_171_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out61;
    _out61 = (client).GetConstraints(_163_input);
    _166_ret = _out61;
    if (!((_166_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(367,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithMyMap(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _173_input;
    _173_input = Helpers_Compile.__default.GetValidInput();
    _173_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_173_input, boxed232 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let116_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed232));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let116_0, boxed233 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _174_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed233));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyMap._typeDescriptor(), Helpers_Compile.__default.ForceMyMap(dafny.DafnyMap.fromElements())), boxed234 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let117_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed234));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let117_0, boxed235 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _175_dt__update_hMyMap_h0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed235));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_174_dt__update__tmp_h0).dtor_MyString(), (_174_dt__update__tmp_h0).dtor_NonEmptyString(), (_174_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_174_dt__update__tmp_h0).dtor_MyBlob(), (_174_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_174_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_174_dt__update__tmp_h0).dtor_MyList(), (_174_dt__update__tmp_h0).dtor_NonEmptyList(), (_174_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), _175_dt__update_hMyMap_h0, (_174_dt__update__tmp_h0).dtor_NonEmptyMap(), (_174_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_174_dt__update__tmp_h0).dtor_OneToTen(), (_174_dt__update__tmp_h0).dtor_myTenToTen(), (_174_dt__update__tmp_h0).dtor_GreaterThanOne(), (_174_dt__update__tmp_h0).dtor_LessThanTen(), (_174_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_174_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _176_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out62;
    _out62 = (client).GetConstraints(_173_input);
    _176_ret = _out62;
    if (!((_176_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(379,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _173_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_173_input, boxed236 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let118_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed236));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let118_0, boxed237 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _177_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed237));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyMap._typeDescriptor(), Helpers_Compile.__default.ForceMyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a"))))), boxed238 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let119_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed238));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let119_0, boxed239 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _178_dt__update_hMyMap_h1 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed239));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_177_dt__update__tmp_h1).dtor_MyString(), (_177_dt__update__tmp_h1).dtor_NonEmptyString(), (_177_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_177_dt__update__tmp_h1).dtor_MyBlob(), (_177_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_177_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_177_dt__update__tmp_h1).dtor_MyList(), (_177_dt__update__tmp_h1).dtor_NonEmptyList(), (_177_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), _178_dt__update_hMyMap_h1, (_177_dt__update__tmp_h1).dtor_NonEmptyMap(), (_177_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_177_dt__update__tmp_h1).dtor_OneToTen(), (_177_dt__update__tmp_h1).dtor_myTenToTen(), (_177_dt__update__tmp_h1).dtor_GreaterThanOne(), (_177_dt__update__tmp_h1).dtor_LessThanTen(), (_177_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_177_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out63;
    _out63 = (client).GetConstraints(_173_input);
    _176_ret = _out63;
    if (!((_176_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(383,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _173_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_173_input, boxed240 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let120_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed240));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let120_0, boxed241 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _179_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed241));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyMap._typeDescriptor(), Helpers_Compile.__default.ForceMyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a"))))), boxed242 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let121_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed242));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let121_0, boxed243 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _180_dt__update_hMyMap_h2 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed243));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_179_dt__update__tmp_h2).dtor_MyString(), (_179_dt__update__tmp_h2).dtor_NonEmptyString(), (_179_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_179_dt__update__tmp_h2).dtor_MyBlob(), (_179_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_179_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_179_dt__update__tmp_h2).dtor_MyList(), (_179_dt__update__tmp_h2).dtor_NonEmptyList(), (_179_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), _180_dt__update_hMyMap_h2, (_179_dt__update__tmp_h2).dtor_NonEmptyMap(), (_179_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_179_dt__update__tmp_h2).dtor_OneToTen(), (_179_dt__update__tmp_h2).dtor_myTenToTen(), (_179_dt__update__tmp_h2).dtor_GreaterThanOne(), (_179_dt__update__tmp_h2).dtor_LessThanTen(), (_179_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_179_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out64;
    _out64 = (client).GetConstraints(_173_input);
    _176_ret = _out64;
    if (!((_176_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(387,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _173_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_173_input, boxed244 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let122_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed244));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let122_0, boxed245 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _181_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed245));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MyMap._typeDescriptor(), Helpers_Compile.__default.ForceMyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("a"), dafny.DafnySequence.asString("a"))))), boxed246 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let123_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed246));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let123_0, boxed247 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _182_dt__update_hMyMap_h3 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed247));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_181_dt__update__tmp_h3).dtor_MyString(), (_181_dt__update__tmp_h3).dtor_NonEmptyString(), (_181_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_181_dt__update__tmp_h3).dtor_MyBlob(), (_181_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_181_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_181_dt__update__tmp_h3).dtor_MyList(), (_181_dt__update__tmp_h3).dtor_NonEmptyList(), (_181_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), _182_dt__update_hMyMap_h3, (_181_dt__update__tmp_h3).dtor_NonEmptyMap(), (_181_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_181_dt__update__tmp_h3).dtor_OneToTen(), (_181_dt__update__tmp_h3).dtor_myTenToTen(), (_181_dt__update__tmp_h3).dtor_GreaterThanOne(), (_181_dt__update__tmp_h3).dtor_LessThanTen(), (_181_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_181_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out65;
    _out65 = (client).GetConstraints(_173_input);
    _176_ret = _out65;
    if (!((_176_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(391,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithNonEmptyMap(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _183_input;
    _183_input = Helpers_Compile.__default.GetValidInput();
    _183_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_183_input, boxed248 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let124_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed248));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let124_0, boxed249 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _184_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed249));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyMap._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyMap(dafny.DafnyMap.fromElements())), boxed250 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let125_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed250));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let125_0, boxed251 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _185_dt__update_hNonEmptyMap_h0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed251));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_184_dt__update__tmp_h0).dtor_MyString(), (_184_dt__update__tmp_h0).dtor_NonEmptyString(), (_184_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_184_dt__update__tmp_h0).dtor_MyBlob(), (_184_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_184_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_184_dt__update__tmp_h0).dtor_MyList(), (_184_dt__update__tmp_h0).dtor_NonEmptyList(), (_184_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_184_dt__update__tmp_h0).dtor_MyMap(), _185_dt__update_hNonEmptyMap_h0, (_184_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_184_dt__update__tmp_h0).dtor_OneToTen(), (_184_dt__update__tmp_h0).dtor_myTenToTen(), (_184_dt__update__tmp_h0).dtor_GreaterThanOne(), (_184_dt__update__tmp_h0).dtor_LessThanTen(), (_184_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_184_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _186_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out66;
    _out66 = (client).GetConstraints(_183_input);
    _186_ret = _out66;
    if (!((_186_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(403,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _183_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_183_input, boxed252 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let126_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed252));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let126_0, boxed253 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _187_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed253));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyMap._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("01234567890"), dafny.DafnySequence.asString("a"))))), boxed254 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let127_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed254));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let127_0, boxed255 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _188_dt__update_hNonEmptyMap_h1 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed255));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_187_dt__update__tmp_h1).dtor_MyString(), (_187_dt__update__tmp_h1).dtor_NonEmptyString(), (_187_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_187_dt__update__tmp_h1).dtor_MyBlob(), (_187_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_187_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_187_dt__update__tmp_h1).dtor_MyList(), (_187_dt__update__tmp_h1).dtor_NonEmptyList(), (_187_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_187_dt__update__tmp_h1).dtor_MyMap(), _188_dt__update_hNonEmptyMap_h1, (_187_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_187_dt__update__tmp_h1).dtor_OneToTen(), (_187_dt__update__tmp_h1).dtor_myTenToTen(), (_187_dt__update__tmp_h1).dtor_GreaterThanOne(), (_187_dt__update__tmp_h1).dtor_LessThanTen(), (_187_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_187_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out67;
    _out67 = (client).GetConstraints(_183_input);
    _186_ret = _out67;
    if (!((_186_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(407,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _183_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_183_input, boxed256 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let128_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed256));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let128_0, boxed257 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _189_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed257));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyMap._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a"))))), boxed258 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let129_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed258));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let129_0, boxed259 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _190_dt__update_hNonEmptyMap_h2 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed259));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_189_dt__update__tmp_h2).dtor_MyString(), (_189_dt__update__tmp_h2).dtor_NonEmptyString(), (_189_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_189_dt__update__tmp_h2).dtor_MyBlob(), (_189_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_189_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_189_dt__update__tmp_h2).dtor_MyList(), (_189_dt__update__tmp_h2).dtor_NonEmptyList(), (_189_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_189_dt__update__tmp_h2).dtor_MyMap(), _190_dt__update_hNonEmptyMap_h2, (_189_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_189_dt__update__tmp_h2).dtor_OneToTen(), (_189_dt__update__tmp_h2).dtor_myTenToTen(), (_189_dt__update__tmp_h2).dtor_GreaterThanOne(), (_189_dt__update__tmp_h2).dtor_LessThanTen(), (_189_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_189_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out68;
    _out68 = (client).GetConstraints(_183_input);
    _186_ret = _out68;
    if (!((_186_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(411,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _183_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_183_input, boxed260 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let130_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed260));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let130_0, boxed261 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _191_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed261));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.NonEmptyMap._typeDescriptor(), Helpers_Compile.__default.ForceNonEmptyMap(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("a"), dafny.DafnySequence.asString("a"))))), boxed262 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let131_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed262));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let131_0, boxed263 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _192_dt__update_hNonEmptyMap_h3 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed263));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_191_dt__update__tmp_h3).dtor_MyString(), (_191_dt__update__tmp_h3).dtor_NonEmptyString(), (_191_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_191_dt__update__tmp_h3).dtor_MyBlob(), (_191_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_191_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_191_dt__update__tmp_h3).dtor_MyList(), (_191_dt__update__tmp_h3).dtor_NonEmptyList(), (_191_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_191_dt__update__tmp_h3).dtor_MyMap(), _192_dt__update_hNonEmptyMap_h3, (_191_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_191_dt__update__tmp_h3).dtor_OneToTen(), (_191_dt__update__tmp_h3).dtor_myTenToTen(), (_191_dt__update__tmp_h3).dtor_GreaterThanOne(), (_191_dt__update__tmp_h3).dtor_LessThanTen(), (_191_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_191_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out69;
    _out69 = (client).GetConstraints(_183_input);
    _186_ret = _out69;
    if (!((_186_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(415,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithMapLessThanOrEqualToTen(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _193_input;
    _193_input = Helpers_Compile.__default.GetValidInput();
    _193_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_193_input, boxed264 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let132_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed264));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let132_0, boxed265 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _194_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed265));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MapLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceMapLessThanOrEqualToTen(dafny.DafnyMap.fromElements())), boxed266 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let133_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed266));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let133_0, boxed267 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _195_dt__update_hMapLessThanOrEqualToTen_h0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed267));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_194_dt__update__tmp_h0).dtor_MyString(), (_194_dt__update__tmp_h0).dtor_NonEmptyString(), (_194_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_194_dt__update__tmp_h0).dtor_MyBlob(), (_194_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_194_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_194_dt__update__tmp_h0).dtor_MyList(), (_194_dt__update__tmp_h0).dtor_NonEmptyList(), (_194_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_194_dt__update__tmp_h0).dtor_MyMap(), (_194_dt__update__tmp_h0).dtor_NonEmptyMap(), _195_dt__update_hMapLessThanOrEqualToTen_h0, (_194_dt__update__tmp_h0).dtor_OneToTen(), (_194_dt__update__tmp_h0).dtor_myTenToTen(), (_194_dt__update__tmp_h0).dtor_GreaterThanOne(), (_194_dt__update__tmp_h0).dtor_LessThanTen(), (_194_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_194_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _196_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out70;
    _out70 = (client).GetConstraints(_193_input);
    _196_ret = _out70;
    if (!((_196_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(427,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _193_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_193_input, boxed268 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let134_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed268));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let134_0, boxed269 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _197_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed269));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MapLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceMapLessThanOrEqualToTen(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a"))))), boxed270 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let135_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed270));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let135_0, boxed271 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _198_dt__update_hMapLessThanOrEqualToTen_h1 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed271));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_197_dt__update__tmp_h1).dtor_MyString(), (_197_dt__update__tmp_h1).dtor_NonEmptyString(), (_197_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_197_dt__update__tmp_h1).dtor_MyBlob(), (_197_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_197_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_197_dt__update__tmp_h1).dtor_MyList(), (_197_dt__update__tmp_h1).dtor_NonEmptyList(), (_197_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_197_dt__update__tmp_h1).dtor_MyMap(), (_197_dt__update__tmp_h1).dtor_NonEmptyMap(), _198_dt__update_hMapLessThanOrEqualToTen_h1, (_197_dt__update__tmp_h1).dtor_OneToTen(), (_197_dt__update__tmp_h1).dtor_myTenToTen(), (_197_dt__update__tmp_h1).dtor_GreaterThanOne(), (_197_dt__update__tmp_h1).dtor_LessThanTen(), (_197_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_197_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out71;
    _out71 = (client).GetConstraints(_193_input);
    _196_ret = _out71;
    if (!((_196_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(431,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _193_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_193_input, boxed272 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let136_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed272));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let136_0, boxed273 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _199_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed273));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MapLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceMapLessThanOrEqualToTen(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a"))))), boxed274 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let137_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed274));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let137_0, boxed275 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _200_dt__update_hMapLessThanOrEqualToTen_h2 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed275));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_199_dt__update__tmp_h2).dtor_MyString(), (_199_dt__update__tmp_h2).dtor_NonEmptyString(), (_199_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_199_dt__update__tmp_h2).dtor_MyBlob(), (_199_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_199_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_199_dt__update__tmp_h2).dtor_MyList(), (_199_dt__update__tmp_h2).dtor_NonEmptyList(), (_199_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_199_dt__update__tmp_h2).dtor_MyMap(), (_199_dt__update__tmp_h2).dtor_NonEmptyMap(), _200_dt__update_hMapLessThanOrEqualToTen_h2, (_199_dt__update__tmp_h2).dtor_OneToTen(), (_199_dt__update__tmp_h2).dtor_myTenToTen(), (_199_dt__update__tmp_h2).dtor_GreaterThanOne(), (_199_dt__update__tmp_h2).dtor_LessThanTen(), (_199_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_199_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out72;
    _out72 = (client).GetConstraints(_193_input);
    _196_ret = _out72;
    if (!((_196_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(435,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _193_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_193_input, boxed276 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let138_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed276));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let138_0, boxed277 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _201_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed277));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(simple.constraints.internaldafny.types.MapLessThanOrEqualToTen._typeDescriptor(), Helpers_Compile.__default.ForceMapLessThanOrEqualToTen(dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("1"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("3"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("4"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("5"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("6"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("7"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("8"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("9"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("a")), new dafny.Tuple2(dafny.DafnySequence.asString("a"), dafny.DafnySequence.asString("a"))))), boxed278 -> {
          Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _pat_let139_0 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed278));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let139_0, boxed279 -> {
            Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _202_dt__update_hMapLessThanOrEqualToTen_h3 = ((Wrappers_Compile.Option<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>)(java.lang.Object)(boxed279));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_201_dt__update__tmp_h3).dtor_MyString(), (_201_dt__update__tmp_h3).dtor_NonEmptyString(), (_201_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_201_dt__update__tmp_h3).dtor_MyBlob(), (_201_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_201_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_201_dt__update__tmp_h3).dtor_MyList(), (_201_dt__update__tmp_h3).dtor_NonEmptyList(), (_201_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_201_dt__update__tmp_h3).dtor_MyMap(), (_201_dt__update__tmp_h3).dtor_NonEmptyMap(), _202_dt__update_hMapLessThanOrEqualToTen_h3, (_201_dt__update__tmp_h3).dtor_OneToTen(), (_201_dt__update__tmp_h3).dtor_myTenToTen(), (_201_dt__update__tmp_h3).dtor_GreaterThanOne(), (_201_dt__update__tmp_h3).dtor_LessThanTen(), (_201_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_201_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out73;
    _out73 = (client).GetConstraints(_193_input);
    _196_ret = _out73;
    if (!((_196_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(439,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithGreaterThanOne(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _203_input;
    _203_input = Helpers_Compile.__default.GetValidInput();
    _203_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_203_input, boxed280 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let140_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed280));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let140_0, boxed281 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _204_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed281));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.GreaterThanOne._typeDescriptor(), Helpers_Compile.__default.ForceGreaterThanOne(java.math.BigInteger.valueOf(1000L))), boxed282 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let141_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed282));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let141_0, boxed283 -> {
            Wrappers_Compile.Option<java.lang.Integer> _205_dt__update_hGreaterThanOne_h0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed283));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_204_dt__update__tmp_h0).dtor_MyString(), (_204_dt__update__tmp_h0).dtor_NonEmptyString(), (_204_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_204_dt__update__tmp_h0).dtor_MyBlob(), (_204_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_204_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_204_dt__update__tmp_h0).dtor_MyList(), (_204_dt__update__tmp_h0).dtor_NonEmptyList(), (_204_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_204_dt__update__tmp_h0).dtor_MyMap(), (_204_dt__update__tmp_h0).dtor_NonEmptyMap(), (_204_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_204_dt__update__tmp_h0).dtor_OneToTen(), (_204_dt__update__tmp_h0).dtor_myTenToTen(), _205_dt__update_hGreaterThanOne_h0, (_204_dt__update__tmp_h0).dtor_LessThanTen(), (_204_dt__update__tmp_h0).dtor_MyUtf8Bytes(), (_204_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _206_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out74;
    _out74 = (client).GetConstraints(_203_input);
    _206_ret = _out74;
    if (!((_206_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(451,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _203_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_203_input, boxed284 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let142_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed284));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let142_0, boxed285 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _207_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed285));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.GreaterThanOne._typeDescriptor(), Helpers_Compile.__default.ForceGreaterThanOne(java.math.BigInteger.valueOf(-1000L))), boxed286 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let143_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed286));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let143_0, boxed287 -> {
            Wrappers_Compile.Option<java.lang.Integer> _208_dt__update_hGreaterThanOne_h1 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed287));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_207_dt__update__tmp_h1).dtor_MyString(), (_207_dt__update__tmp_h1).dtor_NonEmptyString(), (_207_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_207_dt__update__tmp_h1).dtor_MyBlob(), (_207_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_207_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_207_dt__update__tmp_h1).dtor_MyList(), (_207_dt__update__tmp_h1).dtor_NonEmptyList(), (_207_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_207_dt__update__tmp_h1).dtor_MyMap(), (_207_dt__update__tmp_h1).dtor_NonEmptyMap(), (_207_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_207_dt__update__tmp_h1).dtor_OneToTen(), (_207_dt__update__tmp_h1).dtor_myTenToTen(), _208_dt__update_hGreaterThanOne_h1, (_207_dt__update__tmp_h1).dtor_LessThanTen(), (_207_dt__update__tmp_h1).dtor_MyUtf8Bytes(), (_207_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out75;
    _out75 = (client).GetConstraints(_203_input);
    _206_ret = _out75;
    if (!((_206_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(455,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _203_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_203_input, boxed288 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let144_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed288));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let144_0, boxed289 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _209_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed289));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.GreaterThanOne._typeDescriptor(), Helpers_Compile.__default.ForceGreaterThanOne(java.math.BigInteger.ZERO)), boxed290 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let145_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed290));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let145_0, boxed291 -> {
            Wrappers_Compile.Option<java.lang.Integer> _210_dt__update_hGreaterThanOne_h2 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed291));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_209_dt__update__tmp_h2).dtor_MyString(), (_209_dt__update__tmp_h2).dtor_NonEmptyString(), (_209_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_209_dt__update__tmp_h2).dtor_MyBlob(), (_209_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_209_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_209_dt__update__tmp_h2).dtor_MyList(), (_209_dt__update__tmp_h2).dtor_NonEmptyList(), (_209_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_209_dt__update__tmp_h2).dtor_MyMap(), (_209_dt__update__tmp_h2).dtor_NonEmptyMap(), (_209_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_209_dt__update__tmp_h2).dtor_OneToTen(), (_209_dt__update__tmp_h2).dtor_myTenToTen(), _210_dt__update_hGreaterThanOne_h2, (_209_dt__update__tmp_h2).dtor_LessThanTen(), (_209_dt__update__tmp_h2).dtor_MyUtf8Bytes(), (_209_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out76;
    _out76 = (client).GetConstraints(_203_input);
    _206_ret = _out76;
    if (!((_206_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(459,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _203_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_203_input, boxed292 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let146_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed292));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let146_0, boxed293 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _211_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed293));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<java.lang.Integer>create_Some(simple.constraints.internaldafny.types.GreaterThanOne._typeDescriptor(), Helpers_Compile.__default.ForceGreaterThanOne(java.math.BigInteger.ONE)), boxed294 -> {
          Wrappers_Compile.Option<java.lang.Integer> _pat_let147_0 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed294));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<java.lang.Integer>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let147_0, boxed295 -> {
            Wrappers_Compile.Option<java.lang.Integer> _212_dt__update_hGreaterThanOne_h3 = ((Wrappers_Compile.Option<java.lang.Integer>)(java.lang.Object)(boxed295));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_211_dt__update__tmp_h3).dtor_MyString(), (_211_dt__update__tmp_h3).dtor_NonEmptyString(), (_211_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_211_dt__update__tmp_h3).dtor_MyBlob(), (_211_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_211_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_211_dt__update__tmp_h3).dtor_MyList(), (_211_dt__update__tmp_h3).dtor_NonEmptyList(), (_211_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_211_dt__update__tmp_h3).dtor_MyMap(), (_211_dt__update__tmp_h3).dtor_NonEmptyMap(), (_211_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_211_dt__update__tmp_h3).dtor_OneToTen(), (_211_dt__update__tmp_h3).dtor_myTenToTen(), _212_dt__update_hGreaterThanOne_h3, (_211_dt__update__tmp_h3).dtor_LessThanTen(), (_211_dt__update__tmp_h3).dtor_MyUtf8Bytes(), (_211_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out77;
    _out77 = (client).GetConstraints(_203_input);
    _206_ret = _out77;
    if (!((_206_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(463,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithUtf8Bytes(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    simple.constraints.internaldafny.types.GetConstraintsInput _213_input;
    _213_input = Helpers_Compile.__default.GetValidInput();
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed296 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let148_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed296));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let148_0, boxed297 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _214_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed297));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor()))), boxed298 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let149_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed298));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let149_0, boxed299 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _215_dt__update_hMyUtf8Bytes_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed299));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_214_dt__update__tmp_h0).dtor_MyString(), (_214_dt__update__tmp_h0).dtor_NonEmptyString(), (_214_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_214_dt__update__tmp_h0).dtor_MyBlob(), (_214_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_214_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_214_dt__update__tmp_h0).dtor_MyList(), (_214_dt__update__tmp_h0).dtor_NonEmptyList(), (_214_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_214_dt__update__tmp_h0).dtor_MyMap(), (_214_dt__update__tmp_h0).dtor_NonEmptyMap(), (_214_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_214_dt__update__tmp_h0).dtor_OneToTen(), (_214_dt__update__tmp_h0).dtor_myTenToTen(), (_214_dt__update__tmp_h0).dtor_GreaterThanOne(), (_214_dt__update__tmp_h0).dtor_LessThanTen(), _215_dt__update_hMyUtf8Bytes_h0, (_214_dt__update__tmp_h0).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _216_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out78;
    _out78 = (client).GetConstraints(_213_input);
    _216_ret = _out78;
    if (!((_216_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(475,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed300 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let150_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed300));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let150_0, boxed301 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _217_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed301));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 1))), boxed302 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let151_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed302));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let151_0, boxed303 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _218_dt__update_hMyUtf8Bytes_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed303));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_217_dt__update__tmp_h1).dtor_MyString(), (_217_dt__update__tmp_h1).dtor_NonEmptyString(), (_217_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_217_dt__update__tmp_h1).dtor_MyBlob(), (_217_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_217_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_217_dt__update__tmp_h1).dtor_MyList(), (_217_dt__update__tmp_h1).dtor_NonEmptyList(), (_217_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_217_dt__update__tmp_h1).dtor_MyMap(), (_217_dt__update__tmp_h1).dtor_NonEmptyMap(), (_217_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_217_dt__update__tmp_h1).dtor_OneToTen(), (_217_dt__update__tmp_h1).dtor_myTenToTen(), (_217_dt__update__tmp_h1).dtor_GreaterThanOne(), (_217_dt__update__tmp_h1).dtor_LessThanTen(), _218_dt__update_hMyUtf8Bytes_h1, (_217_dt__update__tmp_h1).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out79;
    _out79 = (client).GetConstraints(_213_input);
    _216_ret = _out79;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(479,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed304 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let152_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed304));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let152_0, boxed305 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _219_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed305));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0))), boxed306 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let153_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed306));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let153_0, boxed307 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _220_dt__update_hMyUtf8Bytes_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed307));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_219_dt__update__tmp_h2).dtor_MyString(), (_219_dt__update__tmp_h2).dtor_NonEmptyString(), (_219_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_219_dt__update__tmp_h2).dtor_MyBlob(), (_219_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_219_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_219_dt__update__tmp_h2).dtor_MyList(), (_219_dt__update__tmp_h2).dtor_NonEmptyList(), (_219_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_219_dt__update__tmp_h2).dtor_MyMap(), (_219_dt__update__tmp_h2).dtor_NonEmptyMap(), (_219_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_219_dt__update__tmp_h2).dtor_OneToTen(), (_219_dt__update__tmp_h2).dtor_myTenToTen(), (_219_dt__update__tmp_h2).dtor_GreaterThanOne(), (_219_dt__update__tmp_h2).dtor_LessThanTen(), _220_dt__update_hMyUtf8Bytes_h2, (_219_dt__update__tmp_h2).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out80;
    _out80 = (client).GetConstraints(_213_input);
    _216_ret = _out80;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(483,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed308 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let154_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed308));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let154_0, boxed309 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _221_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed309));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3, (byte) 4, (byte) 5, (byte) 6, (byte) 7, (byte) 8, (byte) 9, (byte) 0, (byte) 1))), boxed310 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let155_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed310));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let155_0, boxed311 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _222_dt__update_hMyUtf8Bytes_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed311));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_221_dt__update__tmp_h3).dtor_MyString(), (_221_dt__update__tmp_h3).dtor_NonEmptyString(), (_221_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_221_dt__update__tmp_h3).dtor_MyBlob(), (_221_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_221_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_221_dt__update__tmp_h3).dtor_MyList(), (_221_dt__update__tmp_h3).dtor_NonEmptyList(), (_221_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_221_dt__update__tmp_h3).dtor_MyMap(), (_221_dt__update__tmp_h3).dtor_NonEmptyMap(), (_221_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_221_dt__update__tmp_h3).dtor_OneToTen(), (_221_dt__update__tmp_h3).dtor_myTenToTen(), (_221_dt__update__tmp_h3).dtor_GreaterThanOne(), (_221_dt__update__tmp_h3).dtor_LessThanTen(), _222_dt__update_hMyUtf8Bytes_h3, (_221_dt__update__tmp_h3).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out81;
    _out81 = (client).GetConstraints(_213_input);
    _216_ret = _out81;
    if (!((_216_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(487,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed312 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let156_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed312));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let156_0, boxed313 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _223_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed313));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 255, (byte) 255, (byte) 255))), boxed314 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let157_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed314));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let157_0, boxed315 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _224_dt__update_hMyUtf8Bytes_h4 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed315));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_223_dt__update__tmp_h4).dtor_MyString(), (_223_dt__update__tmp_h4).dtor_NonEmptyString(), (_223_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_223_dt__update__tmp_h4).dtor_MyBlob(), (_223_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_223_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_223_dt__update__tmp_h4).dtor_MyList(), (_223_dt__update__tmp_h4).dtor_NonEmptyList(), (_223_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_223_dt__update__tmp_h4).dtor_MyMap(), (_223_dt__update__tmp_h4).dtor_NonEmptyMap(), (_223_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_223_dt__update__tmp_h4).dtor_OneToTen(), (_223_dt__update__tmp_h4).dtor_myTenToTen(), (_223_dt__update__tmp_h4).dtor_GreaterThanOne(), (_223_dt__update__tmp_h4).dtor_LessThanTen(), _224_dt__update_hMyUtf8Bytes_h4, (_223_dt__update__tmp_h4).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out82;
    _out82 = (client).GetConstraints(_213_input);
    _216_ret = _out82;
    if (!((_216_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(492,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _225_one;
    _225_one = dafny.DafnySequence.<java.lang.Byte> of((byte) 240, (byte) 168, (byte) 137, (byte) 159);
    dafny.DafnySequence<? extends java.lang.Byte> _226_two;
    _226_two = dafny.DafnySequence.<java.lang.Byte> of((byte) 194, (byte) 163);
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv0 = _225_one;
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed316 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let158_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed316));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let158_0, boxed317 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _227_dt__update__tmp_h5 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed317));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(_pat_let_tv0)), boxed318 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let159_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed318));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let159_0, boxed319 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _228_dt__update_hMyUtf8Bytes_h5 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed319));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_227_dt__update__tmp_h5).dtor_MyString(), (_227_dt__update__tmp_h5).dtor_NonEmptyString(), (_227_dt__update__tmp_h5).dtor_StringLessThanOrEqualToTen(), (_227_dt__update__tmp_h5).dtor_MyBlob(), (_227_dt__update__tmp_h5).dtor_NonEmptyBlob(), (_227_dt__update__tmp_h5).dtor_BlobLessThanOrEqualToTen(), (_227_dt__update__tmp_h5).dtor_MyList(), (_227_dt__update__tmp_h5).dtor_NonEmptyList(), (_227_dt__update__tmp_h5).dtor_ListLessThanOrEqualToTen(), (_227_dt__update__tmp_h5).dtor_MyMap(), (_227_dt__update__tmp_h5).dtor_NonEmptyMap(), (_227_dt__update__tmp_h5).dtor_MapLessThanOrEqualToTen(), (_227_dt__update__tmp_h5).dtor_OneToTen(), (_227_dt__update__tmp_h5).dtor_myTenToTen(), (_227_dt__update__tmp_h5).dtor_GreaterThanOne(), (_227_dt__update__tmp_h5).dtor_LessThanTen(), _228_dt__update_hMyUtf8Bytes_h5, (_227_dt__update__tmp_h5).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out83;
    _out83 = (client).GetConstraints(_213_input);
    _216_ret = _out83;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(498,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv1 = _225_one;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv2 = _225_one;
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed320 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let160_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed320));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let160_0, boxed321 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _229_dt__update__tmp_h6 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed321));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte>concatenate(_pat_let_tv1, _pat_let_tv2))), boxed322 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let161_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed322));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let161_0, boxed323 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _230_dt__update_hMyUtf8Bytes_h6 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed323));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_229_dt__update__tmp_h6).dtor_MyString(), (_229_dt__update__tmp_h6).dtor_NonEmptyString(), (_229_dt__update__tmp_h6).dtor_StringLessThanOrEqualToTen(), (_229_dt__update__tmp_h6).dtor_MyBlob(), (_229_dt__update__tmp_h6).dtor_NonEmptyBlob(), (_229_dt__update__tmp_h6).dtor_BlobLessThanOrEqualToTen(), (_229_dt__update__tmp_h6).dtor_MyList(), (_229_dt__update__tmp_h6).dtor_NonEmptyList(), (_229_dt__update__tmp_h6).dtor_ListLessThanOrEqualToTen(), (_229_dt__update__tmp_h6).dtor_MyMap(), (_229_dt__update__tmp_h6).dtor_NonEmptyMap(), (_229_dt__update__tmp_h6).dtor_MapLessThanOrEqualToTen(), (_229_dt__update__tmp_h6).dtor_OneToTen(), (_229_dt__update__tmp_h6).dtor_myTenToTen(), (_229_dt__update__tmp_h6).dtor_GreaterThanOne(), (_229_dt__update__tmp_h6).dtor_LessThanTen(), _230_dt__update_hMyUtf8Bytes_h6, (_229_dt__update__tmp_h6).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out84;
    _out84 = (client).GetConstraints(_213_input);
    _216_ret = _out84;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(502,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv3 = _225_one;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv4 = _225_one;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv5 = _225_one;
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed324 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let162_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed324));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let162_0, boxed325 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _231_dt__update__tmp_h7 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed325));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(_pat_let_tv3, _pat_let_tv4), _pat_let_tv5))), boxed326 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let163_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed326));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let163_0, boxed327 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _232_dt__update_hMyUtf8Bytes_h7 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed327));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_231_dt__update__tmp_h7).dtor_MyString(), (_231_dt__update__tmp_h7).dtor_NonEmptyString(), (_231_dt__update__tmp_h7).dtor_StringLessThanOrEqualToTen(), (_231_dt__update__tmp_h7).dtor_MyBlob(), (_231_dt__update__tmp_h7).dtor_NonEmptyBlob(), (_231_dt__update__tmp_h7).dtor_BlobLessThanOrEqualToTen(), (_231_dt__update__tmp_h7).dtor_MyList(), (_231_dt__update__tmp_h7).dtor_NonEmptyList(), (_231_dt__update__tmp_h7).dtor_ListLessThanOrEqualToTen(), (_231_dt__update__tmp_h7).dtor_MyMap(), (_231_dt__update__tmp_h7).dtor_NonEmptyMap(), (_231_dt__update__tmp_h7).dtor_MapLessThanOrEqualToTen(), (_231_dt__update__tmp_h7).dtor_OneToTen(), (_231_dt__update__tmp_h7).dtor_myTenToTen(), (_231_dt__update__tmp_h7).dtor_GreaterThanOne(), (_231_dt__update__tmp_h7).dtor_LessThanTen(), _232_dt__update_hMyUtf8Bytes_h7, (_231_dt__update__tmp_h7).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out85;
    _out85 = (client).GetConstraints(_213_input);
    _216_ret = _out85;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(507,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv6 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv7 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv8 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv9 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv10 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv11 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv12 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv13 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv14 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv15 = _226_two;
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed328 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let164_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed328));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let164_0, boxed329 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _233_dt__update__tmp_h8 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed329));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(_pat_let_tv6, _pat_let_tv7), _pat_let_tv8), _pat_let_tv9), _pat_let_tv10), _pat_let_tv11), _pat_let_tv12), _pat_let_tv13), _pat_let_tv14), _pat_let_tv15))), boxed330 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let165_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed330));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let165_0, boxed331 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _234_dt__update_hMyUtf8Bytes_h8 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed331));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_233_dt__update__tmp_h8).dtor_MyString(), (_233_dt__update__tmp_h8).dtor_NonEmptyString(), (_233_dt__update__tmp_h8).dtor_StringLessThanOrEqualToTen(), (_233_dt__update__tmp_h8).dtor_MyBlob(), (_233_dt__update__tmp_h8).dtor_NonEmptyBlob(), (_233_dt__update__tmp_h8).dtor_BlobLessThanOrEqualToTen(), (_233_dt__update__tmp_h8).dtor_MyList(), (_233_dt__update__tmp_h8).dtor_NonEmptyList(), (_233_dt__update__tmp_h8).dtor_ListLessThanOrEqualToTen(), (_233_dt__update__tmp_h8).dtor_MyMap(), (_233_dt__update__tmp_h8).dtor_NonEmptyMap(), (_233_dt__update__tmp_h8).dtor_MapLessThanOrEqualToTen(), (_233_dt__update__tmp_h8).dtor_OneToTen(), (_233_dt__update__tmp_h8).dtor_myTenToTen(), (_233_dt__update__tmp_h8).dtor_GreaterThanOne(), (_233_dt__update__tmp_h8).dtor_LessThanTen(), _234_dt__update_hMyUtf8Bytes_h8, (_233_dt__update__tmp_h8).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out86;
    _out86 = (client).GetConstraints(_213_input);
    _216_ret = _out86;
    if (!((_216_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(511,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv16 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv17 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv18 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv19 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv20 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv21 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv22 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv23 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv24 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv25 = _226_two;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv26 = _226_two;
    _213_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_213_input, boxed332 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let166_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed332));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let166_0, boxed333 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _235_dt__update__tmp_h9 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed333));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte>concatenate(_pat_let_tv16, _pat_let_tv17), _pat_let_tv18), _pat_let_tv19), _pat_let_tv20), _pat_let_tv21), _pat_let_tv22), _pat_let_tv23), _pat_let_tv24), _pat_let_tv25), _pat_let_tv26))), boxed334 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _pat_let167_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed334));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let167_0, boxed335 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>> _236_dt__update_hMyUtf8Bytes_h9 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends java.lang.Byte>>)(java.lang.Object)(boxed335));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_235_dt__update__tmp_h9).dtor_MyString(), (_235_dt__update__tmp_h9).dtor_NonEmptyString(), (_235_dt__update__tmp_h9).dtor_StringLessThanOrEqualToTen(), (_235_dt__update__tmp_h9).dtor_MyBlob(), (_235_dt__update__tmp_h9).dtor_NonEmptyBlob(), (_235_dt__update__tmp_h9).dtor_BlobLessThanOrEqualToTen(), (_235_dt__update__tmp_h9).dtor_MyList(), (_235_dt__update__tmp_h9).dtor_NonEmptyList(), (_235_dt__update__tmp_h9).dtor_ListLessThanOrEqualToTen(), (_235_dt__update__tmp_h9).dtor_MyMap(), (_235_dt__update__tmp_h9).dtor_NonEmptyMap(), (_235_dt__update__tmp_h9).dtor_MapLessThanOrEqualToTen(), (_235_dt__update__tmp_h9).dtor_OneToTen(), (_235_dt__update__tmp_h9).dtor_myTenToTen(), (_235_dt__update__tmp_h9).dtor_GreaterThanOne(), (_235_dt__update__tmp_h9).dtor_LessThanTen(), _236_dt__update_hMyUtf8Bytes_h9, (_235_dt__update__tmp_h9).dtor_MyListOfUtf8Bytes());
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out87;
    _out87 = (client).GetConstraints(_213_input);
    _216_ret = _out87;
    if (!((_216_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(515,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestGetConstraintWithListOfUtf8Bytes(simple.constraints.internaldafny.types.ISimpleConstraintsClient client)
  {
    dafny.DafnySequence<? extends java.lang.Byte> _237_bad;
    _237_bad = Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 255, (byte) 255, (byte) 255));
    dafny.DafnySequence<? extends java.lang.Byte> _238_good;
    _238_good = Helpers_Compile.__default.ForceUtf8Bytes(dafny.DafnySequence.<java.lang.Byte> of((byte) 1, (byte) 2, (byte) 3));
    simple.constraints.internaldafny.types.GetConstraintsInput _239_input;
    _239_input = Helpers_Compile.__default.GetValidInput();
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed336 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let168_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed336));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let168_0, boxed337 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _240_dt__update__tmp_h0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed337));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor()))), boxed338 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let169_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed338));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let169_0, boxed339 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _241_dt__update_hMyListOfUtf8Bytes_h0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed339));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_240_dt__update__tmp_h0).dtor_MyString(), (_240_dt__update__tmp_h0).dtor_NonEmptyString(), (_240_dt__update__tmp_h0).dtor_StringLessThanOrEqualToTen(), (_240_dt__update__tmp_h0).dtor_MyBlob(), (_240_dt__update__tmp_h0).dtor_NonEmptyBlob(), (_240_dt__update__tmp_h0).dtor_BlobLessThanOrEqualToTen(), (_240_dt__update__tmp_h0).dtor_MyList(), (_240_dt__update__tmp_h0).dtor_NonEmptyList(), (_240_dt__update__tmp_h0).dtor_ListLessThanOrEqualToTen(), (_240_dt__update__tmp_h0).dtor_MyMap(), (_240_dt__update__tmp_h0).dtor_NonEmptyMap(), (_240_dt__update__tmp_h0).dtor_MapLessThanOrEqualToTen(), (_240_dt__update__tmp_h0).dtor_OneToTen(), (_240_dt__update__tmp_h0).dtor_myTenToTen(), (_240_dt__update__tmp_h0).dtor_GreaterThanOne(), (_240_dt__update__tmp_h0).dtor_LessThanTen(), (_240_dt__update__tmp_h0).dtor_MyUtf8Bytes(), _241_dt__update_hMyListOfUtf8Bytes_h0);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _242_ret;
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out88;
    _out88 = (client).GetConstraints(_239_input);
    _242_ret = _out88;
    if (!((_242_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(542,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv27 = _238_good;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed340 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let170_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed340));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let170_0, boxed341 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _243_dt__update__tmp_h1 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed341));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv27))), boxed342 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let171_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed342));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let171_0, boxed343 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _244_dt__update_hMyListOfUtf8Bytes_h1 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed343));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_243_dt__update__tmp_h1).dtor_MyString(), (_243_dt__update__tmp_h1).dtor_NonEmptyString(), (_243_dt__update__tmp_h1).dtor_StringLessThanOrEqualToTen(), (_243_dt__update__tmp_h1).dtor_MyBlob(), (_243_dt__update__tmp_h1).dtor_NonEmptyBlob(), (_243_dt__update__tmp_h1).dtor_BlobLessThanOrEqualToTen(), (_243_dt__update__tmp_h1).dtor_MyList(), (_243_dt__update__tmp_h1).dtor_NonEmptyList(), (_243_dt__update__tmp_h1).dtor_ListLessThanOrEqualToTen(), (_243_dt__update__tmp_h1).dtor_MyMap(), (_243_dt__update__tmp_h1).dtor_NonEmptyMap(), (_243_dt__update__tmp_h1).dtor_MapLessThanOrEqualToTen(), (_243_dt__update__tmp_h1).dtor_OneToTen(), (_243_dt__update__tmp_h1).dtor_myTenToTen(), (_243_dt__update__tmp_h1).dtor_GreaterThanOne(), (_243_dt__update__tmp_h1).dtor_LessThanTen(), (_243_dt__update__tmp_h1).dtor_MyUtf8Bytes(), _244_dt__update_hMyListOfUtf8Bytes_h1);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out89;
    _out89 = (client).GetConstraints(_239_input);
    _242_ret = _out89;
    if (!((_242_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(546,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv28 = _238_good;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv29 = _238_good;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed344 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let172_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed344));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let172_0, boxed345 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _245_dt__update__tmp_h2 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed345));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv28, _pat_let_tv29))), boxed346 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let173_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed346));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let173_0, boxed347 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _246_dt__update_hMyListOfUtf8Bytes_h2 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed347));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_245_dt__update__tmp_h2).dtor_MyString(), (_245_dt__update__tmp_h2).dtor_NonEmptyString(), (_245_dt__update__tmp_h2).dtor_StringLessThanOrEqualToTen(), (_245_dt__update__tmp_h2).dtor_MyBlob(), (_245_dt__update__tmp_h2).dtor_NonEmptyBlob(), (_245_dt__update__tmp_h2).dtor_BlobLessThanOrEqualToTen(), (_245_dt__update__tmp_h2).dtor_MyList(), (_245_dt__update__tmp_h2).dtor_NonEmptyList(), (_245_dt__update__tmp_h2).dtor_ListLessThanOrEqualToTen(), (_245_dt__update__tmp_h2).dtor_MyMap(), (_245_dt__update__tmp_h2).dtor_NonEmptyMap(), (_245_dt__update__tmp_h2).dtor_MapLessThanOrEqualToTen(), (_245_dt__update__tmp_h2).dtor_OneToTen(), (_245_dt__update__tmp_h2).dtor_myTenToTen(), (_245_dt__update__tmp_h2).dtor_GreaterThanOne(), (_245_dt__update__tmp_h2).dtor_LessThanTen(), (_245_dt__update__tmp_h2).dtor_MyUtf8Bytes(), _246_dt__update_hMyListOfUtf8Bytes_h2);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out90;
    _out90 = (client).GetConstraints(_239_input);
    _242_ret = _out90;
    if (!((_242_ret).is_Success())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(550,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv30 = _238_good;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv31 = _238_good;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv32 = _238_good;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed348 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let174_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed348));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let174_0, boxed349 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _247_dt__update__tmp_h3 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed349));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv30, _pat_let_tv31, _pat_let_tv32))), boxed350 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let175_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed350));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let175_0, boxed351 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _248_dt__update_hMyListOfUtf8Bytes_h3 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed351));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_247_dt__update__tmp_h3).dtor_MyString(), (_247_dt__update__tmp_h3).dtor_NonEmptyString(), (_247_dt__update__tmp_h3).dtor_StringLessThanOrEqualToTen(), (_247_dt__update__tmp_h3).dtor_MyBlob(), (_247_dt__update__tmp_h3).dtor_NonEmptyBlob(), (_247_dt__update__tmp_h3).dtor_BlobLessThanOrEqualToTen(), (_247_dt__update__tmp_h3).dtor_MyList(), (_247_dt__update__tmp_h3).dtor_NonEmptyList(), (_247_dt__update__tmp_h3).dtor_ListLessThanOrEqualToTen(), (_247_dt__update__tmp_h3).dtor_MyMap(), (_247_dt__update__tmp_h3).dtor_NonEmptyMap(), (_247_dt__update__tmp_h3).dtor_MapLessThanOrEqualToTen(), (_247_dt__update__tmp_h3).dtor_OneToTen(), (_247_dt__update__tmp_h3).dtor_myTenToTen(), (_247_dt__update__tmp_h3).dtor_GreaterThanOne(), (_247_dt__update__tmp_h3).dtor_LessThanTen(), (_247_dt__update__tmp_h3).dtor_MyUtf8Bytes(), _248_dt__update_hMyListOfUtf8Bytes_h3);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out91;
    _out91 = (client).GetConstraints(_239_input);
    _242_ret = _out91;
    if (!((_242_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(554,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv33 = _237_bad;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed352 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let176_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed352));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let176_0, boxed353 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _249_dt__update__tmp_h4 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed353));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv33))), boxed354 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let177_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed354));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let177_0, boxed355 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _250_dt__update_hMyListOfUtf8Bytes_h4 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed355));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_249_dt__update__tmp_h4).dtor_MyString(), (_249_dt__update__tmp_h4).dtor_NonEmptyString(), (_249_dt__update__tmp_h4).dtor_StringLessThanOrEqualToTen(), (_249_dt__update__tmp_h4).dtor_MyBlob(), (_249_dt__update__tmp_h4).dtor_NonEmptyBlob(), (_249_dt__update__tmp_h4).dtor_BlobLessThanOrEqualToTen(), (_249_dt__update__tmp_h4).dtor_MyList(), (_249_dt__update__tmp_h4).dtor_NonEmptyList(), (_249_dt__update__tmp_h4).dtor_ListLessThanOrEqualToTen(), (_249_dt__update__tmp_h4).dtor_MyMap(), (_249_dt__update__tmp_h4).dtor_NonEmptyMap(), (_249_dt__update__tmp_h4).dtor_MapLessThanOrEqualToTen(), (_249_dt__update__tmp_h4).dtor_OneToTen(), (_249_dt__update__tmp_h4).dtor_myTenToTen(), (_249_dt__update__tmp_h4).dtor_GreaterThanOne(), (_249_dt__update__tmp_h4).dtor_LessThanTen(), (_249_dt__update__tmp_h4).dtor_MyUtf8Bytes(), _250_dt__update_hMyListOfUtf8Bytes_h4);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out92;
    _out92 = (client).GetConstraints(_239_input);
    _242_ret = _out92;
    if (!((_242_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(558,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv34 = _237_bad;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv35 = _238_good;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed356 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let178_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed356));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let178_0, boxed357 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _251_dt__update__tmp_h5 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed357));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv34, _pat_let_tv35))), boxed358 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let179_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed358));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let179_0, boxed359 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _252_dt__update_hMyListOfUtf8Bytes_h5 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed359));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_251_dt__update__tmp_h5).dtor_MyString(), (_251_dt__update__tmp_h5).dtor_NonEmptyString(), (_251_dt__update__tmp_h5).dtor_StringLessThanOrEqualToTen(), (_251_dt__update__tmp_h5).dtor_MyBlob(), (_251_dt__update__tmp_h5).dtor_NonEmptyBlob(), (_251_dt__update__tmp_h5).dtor_BlobLessThanOrEqualToTen(), (_251_dt__update__tmp_h5).dtor_MyList(), (_251_dt__update__tmp_h5).dtor_NonEmptyList(), (_251_dt__update__tmp_h5).dtor_ListLessThanOrEqualToTen(), (_251_dt__update__tmp_h5).dtor_MyMap(), (_251_dt__update__tmp_h5).dtor_NonEmptyMap(), (_251_dt__update__tmp_h5).dtor_MapLessThanOrEqualToTen(), (_251_dt__update__tmp_h5).dtor_OneToTen(), (_251_dt__update__tmp_h5).dtor_myTenToTen(), (_251_dt__update__tmp_h5).dtor_GreaterThanOne(), (_251_dt__update__tmp_h5).dtor_LessThanTen(), (_251_dt__update__tmp_h5).dtor_MyUtf8Bytes(), _252_dt__update_hMyListOfUtf8Bytes_h5);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out93;
    _out93 = (client).GetConstraints(_239_input);
    _242_ret = _out93;
    if (!((_242_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(562,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv36 = _238_good;
    dafny.DafnySequence<? extends java.lang.Byte> _pat_let_tv37 = _237_bad;
    _239_input = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_239_input, boxed360 -> {
      simple.constraints.internaldafny.types.GetConstraintsInput _pat_let180_0 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed360));
      return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<simple.constraints.internaldafny.types.GetConstraintsInput, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let180_0, boxed361 -> {
        simple.constraints.internaldafny.types.GetConstraintsInput _253_dt__update__tmp_h6 = ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(boxed361));
        return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(simple.constraints.internaldafny.types.ListOfUtf8Bytes._typeDescriptor(), Helpers_Compile.__default.ForceListOfUtf8Bytes(dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> of(simple.constraints.internaldafny.types.Utf8Bytes._typeDescriptor(), _pat_let_tv36, _pat_let_tv37))), boxed362 -> {
          Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _pat_let181_0 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed362));
          return ((simple.constraints.internaldafny.types.GetConstraintsInput)(java.lang.Object)(dafny.Helpers.<Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>, simple.constraints.internaldafny.types.GetConstraintsInput>Let(_pat_let181_0, boxed363 -> {
            Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _254_dt__update_hMyListOfUtf8Bytes_h6 = ((Wrappers_Compile.Option<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>)(java.lang.Object)(boxed363));
            return simple.constraints.internaldafny.types.GetConstraintsInput.create((_253_dt__update__tmp_h6).dtor_MyString(), (_253_dt__update__tmp_h6).dtor_NonEmptyString(), (_253_dt__update__tmp_h6).dtor_StringLessThanOrEqualToTen(), (_253_dt__update__tmp_h6).dtor_MyBlob(), (_253_dt__update__tmp_h6).dtor_NonEmptyBlob(), (_253_dt__update__tmp_h6).dtor_BlobLessThanOrEqualToTen(), (_253_dt__update__tmp_h6).dtor_MyList(), (_253_dt__update__tmp_h6).dtor_NonEmptyList(), (_253_dt__update__tmp_h6).dtor_ListLessThanOrEqualToTen(), (_253_dt__update__tmp_h6).dtor_MyMap(), (_253_dt__update__tmp_h6).dtor_NonEmptyMap(), (_253_dt__update__tmp_h6).dtor_MapLessThanOrEqualToTen(), (_253_dt__update__tmp_h6).dtor_OneToTen(), (_253_dt__update__tmp_h6).dtor_myTenToTen(), (_253_dt__update__tmp_h6).dtor_GreaterThanOne(), (_253_dt__update__tmp_h6).dtor_LessThanTen(), (_253_dt__update__tmp_h6).dtor_MyUtf8Bytes(), _254_dt__update_hMyListOfUtf8Bytes_h6);
          }
          )));
        }
        )));
      }
      )));
    }
    )));
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out94;
    _out94 = (client).GetConstraints(_239_input);
    _242_ret = _out94;
    if (!((_242_ret).is_Failure())) {
      throw new dafny.DafnyHaltException("test/WrappedSimpleConstraintsTest.dfy(566,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  @Override
  public java.lang.String toString() {
    return "WrappedSimpleConstraintsTest._default";
  }
}
