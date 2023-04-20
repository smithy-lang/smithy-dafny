// Class __default
// Dafny class __default compiled into Java
package Helpers_Compile;

import Dafny.Simple.Dependencies.Wrapped.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Dafny.Simple.Constraints.Types.GetConstraintsInput GetConstraintsInputTemplate(dafny.DafnySet<? extends dafny.DafnySequence<? extends Character>> overrideToInvalidInput)
  {
    Dafny.Simple.Constraints.Types.GetConstraintsInput output = Dafny.Simple.Constraints.Types.GetConstraintsInput.Default();
    boolean _0_overrideMyString;
    _0_overrideMyString = (overrideToInvalidInput).<dafny.DafnySequence<? extends Character>>contains(dafny.DafnySequence.asString("myString"));
    dafny.DafnySequence<? extends Character> _1_myString = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    if (_0_overrideMyString) {
      dafny.DafnySequence<? extends Character> _out0;
      _out0 = __default.InvalidMyStringInput();
      _1_myString = _out0;
    } else {
      _1_myString = dafny.DafnySequence.asString("bw1and10");
    }
    boolean _2_overrideNonEmptyString;
    _2_overrideNonEmptyString = (overrideToInvalidInput).<dafny.DafnySequence<? extends Character>>contains(dafny.DafnySequence.asString("nonEmptyString"));
    dafny.DafnySequence<? extends Character> _3_nonEmptyString = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    if (_2_overrideNonEmptyString) {
      dafny.DafnySequence<? extends Character> _out1;
      _out1 = __default.InvalidNonEmptyStringInput();
      _3_nonEmptyString = _out1;
    } else {
      _3_nonEmptyString = dafny.DafnySequence.asString("atleast1");
    }
    boolean _4_overrideStringLessThanOrEqualToTen;
    _4_overrideStringLessThanOrEqualToTen = (overrideToInvalidInput).<dafny.DafnySequence<? extends Character>>contains(dafny.DafnySequence.asString("overrideStringLessThanOrEqualToTen"));
    dafny.DafnySequence<? extends Character> _5_stringLessThanOrEqualToTen = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    if (_4_overrideStringLessThanOrEqualToTen) {
      dafny.DafnySequence<? extends Character> _out2;
      _out2 = __default.InvalidStringLessThanOrEqualToTen();
      _5_stringLessThanOrEqualToTen = _out2;
    } else {
      _5_stringLessThanOrEqualToTen = dafny.DafnySequence.asString("leq10");
    }
    boolean _6_overrideMyBlob;
    _6_overrideMyBlob = (overrideToInvalidInput).<dafny.DafnySequence<? extends Character>>contains(dafny.DafnySequence.asString("myBlob"));
    dafny.DafnySequence<? extends java.lang.Byte> _7_myBlob = dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_mUInt_Compile.uint8._typeDescriptor());
    if (_6_overrideMyBlob) {
      dafny.DafnySequence<? extends java.lang.Byte> _out3;
      _out3 = __default.InvalidMyBlob();
      _7_myBlob = _out3;
    } else {
      _7_myBlob = dafny.DafnySequence.of((byte) 0, (byte) 1, (byte) 0, (byte) 1);
    }
    dafny.DafnySequence<? extends java.lang.Byte> _8_nonEmptyBlob;
    _8_nonEmptyBlob = dafny.DafnySequence.of((byte) 0, (byte) 1, (byte) 0, (byte) 1);
    dafny.DafnySequence<? extends java.lang.Byte> _9_BlobLessThanOrEqualToTen;
    _9_BlobLessThanOrEqualToTen = dafny.DafnySequence.of((byte) 0, (byte) 1, (byte) 0, (byte) 1);
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> _10_myList;
    _10_myList = dafny.DafnySequence.of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("00"), dafny.DafnySequence.asString("11"));
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> _11_nonEmptyList;
    _11_nonEmptyList = dafny.DafnySequence.of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("00"), dafny.DafnySequence.asString("11"));
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> _12_listLessThanOrEqualToTen;
    _12_listLessThanOrEqualToTen = dafny.DafnySequence.of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("00"), dafny.DafnySequence.asString("11"));
    dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> _13_myMap;
    _13_myMap = dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("1")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3")));
    dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> _14_nonEmptyMap;
    _14_nonEmptyMap = dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("1")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3")));
    dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> _15_mapLessThanOrEqualToTen;
    _15_mapLessThanOrEqualToTen = dafny.DafnyMap.fromElements(new dafny.Tuple2(dafny.DafnySequence.asString("0"), dafny.DafnySequence.asString("1")), new dafny.Tuple2(dafny.DafnySequence.asString("2"), dafny.DafnySequence.asString("3")));
    dafny.DafnySequence<? extends Character> _16_alphabetic;
    _16_alphabetic = dafny.DafnySequence.asString("alphabetic");
    int _17_oneToTen;
    _17_oneToTen = 3;
    int _18_greaterThanOne;
    _18_greaterThanOne = 2;
    int _19_lessThanTen;
    _19_lessThanTen = 3;
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> _20_myUniqueList;
    _20_myUniqueList = dafny.DafnySequence.of(dafny.DafnySequence.<Character>_typeDescriptor(dafny.TypeDescriptor.CHAR), dafny.DafnySequence.asString("one"), dafny.DafnySequence.asString("two"));
    dafny.DafnySequence<? extends Dafny.Simple.Constraints.Types.ComplexListElement> _21_myComplexUniqueList;
    _21_myComplexUniqueList = dafny.DafnySequence.of(Dafny.Simple.Constraints.Types.ComplexListElement._typeDescriptor(), Dafny.Simple.Constraints.Types.ComplexListElement.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("one")), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.of((byte) 1, (byte) 1))), Dafny.Simple.Constraints.Types.ComplexListElement.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("two")), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.of((byte) 2, (byte) 2))));
    Dafny.Simple.Constraints.Types.GetConstraintsInput _22_input;
    _22_input = Dafny.Simple.Constraints.Types.GetConstraintsInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(_1_myString), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(_3_nonEmptyString), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(_5_stringLessThanOrEqualToTen), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(_7_myBlob), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(_8_nonEmptyBlob), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(_9_BlobLessThanOrEqualToTen), Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(_10_myList), Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(_11_nonEmptyList), Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(_12_listLessThanOrEqualToTen), Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(_13_myMap), Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(_14_nonEmptyMap), Wrappers_Compile.Option.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>create_Some(_15_mapLessThanOrEqualToTen), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(_16_alphabetic), Wrappers_Compile.Option.<java.lang.Integer>create_Some(_17_oneToTen), Wrappers_Compile.Option.<java.lang.Integer>create_Some(_18_greaterThanOne), Wrappers_Compile.Option.<java.lang.Integer>create_Some(_19_lessThanTen), Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>create_Some(_20_myUniqueList), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Dafny.Simple.Constraints.Types.ComplexListElement>>create_Some(_21_myComplexUniqueList), Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(__default.PROVIDER__ID()), Wrappers_Compile.Option.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>create_Some(dafny.DafnySequence.of(UTF8.ValidUTF8Bytes._typeDescriptor(), __default.PROVIDER__ID(), __default.PROVIDER__ID())));
    output = _22_input;
    return output;
  }
  public static int InvalidLessThanTenInput()
  {
    int invalid = 0;
    int _23_invalidLessThanTenInput;
    _23_invalidLessThanTenInput = 12;
    int _24_invalidLessThanTen;
    _24_invalidLessThanTen = _23_invalidLessThanTenInput;
    invalid = _24_invalidLessThanTen;
    return invalid;
  }
  public static dafny.DafnySequence<? extends Character> InvalidMyStringInput()
  {
    dafny.DafnySequence<? extends Character> invalid = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    dafny.DafnySequence<? extends Character> _25_invalidMyStringInput;
    _25_invalidMyStringInput = dafny.DafnySequence.asString("thisislongerthan10characters");
    dafny.DafnySequence<? extends Character> _26_invalidMyString;
    _26_invalidMyString = _25_invalidMyStringInput;
    invalid = _26_invalidMyString;
    return invalid;
  }
  public static dafny.DafnySequence<? extends Character> InvalidNonEmptyStringInput()
  {
    dafny.DafnySequence<? extends Character> invalid = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    dafny.DafnySequence<? extends Character> _27_invalidNonEmptyStringInput;
    _27_invalidNonEmptyStringInput = dafny.DafnySequence.asString("");
    dafny.DafnySequence<? extends Character> _28_invalidNonEmptyString;
    _28_invalidNonEmptyString = _27_invalidNonEmptyStringInput;
    invalid = _28_invalidNonEmptyString;
    return invalid;
  }
  public static dafny.DafnySequence<? extends Character> InvalidStringLessThanOrEqualToTen()
  {
    dafny.DafnySequence<? extends Character> invalid = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    dafny.DafnySequence<? extends Character> _29_invalidStringLessThanOrEqualToTenInput;
    _29_invalidStringLessThanOrEqualToTenInput = dafny.DafnySequence.asString("");
    dafny.DafnySequence<? extends Character> _30_invalidStringLessThanOrEqualToTen;
    _30_invalidStringLessThanOrEqualToTen = _29_invalidStringLessThanOrEqualToTenInput;
    invalid = _30_invalidStringLessThanOrEqualToTen;
    return invalid;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> InvalidMyBlob()
  {
    dafny.DafnySequence<? extends java.lang.Byte> invalid = dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_mUInt_Compile.uint8._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Byte> _31_invalidMyBlobInput;
    _31_invalidMyBlobInput = dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_mUInt_Compile.uint8._typeDescriptor());
    dafny.DafnySequence<? extends java.lang.Byte> _32_invalidMyBlob;
    _32_invalidMyBlob = _31_invalidMyBlobInput;
    invalid = _32_invalidMyBlob;
    return invalid;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> PROVIDER__ID()
  {
    dafny.DafnySequence<? extends java.lang.Byte> _33_s = dafny.DafnySequence.of((byte) 97, (byte) 119, (byte) 115, (byte) 45, (byte) 107, (byte) 109, (byte) 115);
    return _33_s;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Helpers_Compile._default";
  }
}
