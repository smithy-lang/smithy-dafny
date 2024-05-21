// Package Helpers
// Dafny module Helpers compiled into Go

package Helpers

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Wrappers "Wrappers"
  StandardLibrary_mUInt "StandardLibrary_mUInt"
  StandardLibrary "StandardLibrary"
  UTF8 "UTF8"
  simple.constraints.internaldafny.types "simple.constraints.internaldafny.types"
  SimpleConstraintsImpl "SimpleConstraintsImpl"
  simpleconstraintsinternaldafny "simpleconstraintsinternaldafny"
  simpleconstraintsinternaldafnywrapped "simpleconstraintsinternaldafnywrapped"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleConstraintsImpl.Dummy__

type Dummy__ struct{}


// Definition of class Default__
type Default__ struct {
  dummy byte
}

func New_Default___() *Default__ {
  _this := Default__{}

  return &_this
}

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_this *Default__) Equals(other *Default__) bool {
  return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Default__)
  return ok && _this.Equals(other)
}

func (*Default__) String() string {
  return "Helpers.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetConstraintsInputTemplate(overrideToInvalidInput _dafny.Set) simple.constraints.internaldafny.types.GetConstraintsInput {
  var output simple.constraints.internaldafny.types.GetConstraintsInput = simple.constraints.internaldafny.types.Companion_GetConstraintsInput_.Default()
  _ = output
  var _74_overrideMyString bool
  _ = _74_overrideMyString
  _74_overrideMyString = (overrideToInvalidInput).Contains(_dafny.SeqOfString("myString"))
  var _75_myString _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = _75_myString
  if (_74_overrideMyString) {
    var _out1 _dafny.Sequence
    _ = _out1
    _out1 = Companion_Default___.InvalidMyStringInput()
    _75_myString = _out1
  } else {
    _75_myString = _dafny.SeqOfString("bw1and10")
  }
  var _76_overrideNonEmptyString bool
  _ = _76_overrideNonEmptyString
  _76_overrideNonEmptyString = (overrideToInvalidInput).Contains(_dafny.SeqOfString("nonEmptyString"))
  var _77_nonEmptyString _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = _77_nonEmptyString
  if (_76_overrideNonEmptyString) {
    var _out2 _dafny.Sequence
    _ = _out2
    _out2 = Companion_Default___.InvalidNonEmptyStringInput()
    _77_nonEmptyString = _out2
  } else {
    _77_nonEmptyString = _dafny.SeqOfString("atleast1")
  }
  var _78_overrideStringLessThanOrEqualToTen bool
  _ = _78_overrideStringLessThanOrEqualToTen
  _78_overrideStringLessThanOrEqualToTen = (overrideToInvalidInput).Contains(_dafny.SeqOfString("overrideStringLessThanOrEqualToTen"))
  var _79_stringLessThanOrEqualToTen _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = _79_stringLessThanOrEqualToTen
  if (_78_overrideStringLessThanOrEqualToTen) {
    var _out3 _dafny.Sequence
    _ = _out3
    _out3 = Companion_Default___.InvalidStringLessThanOrEqualToTen()
    _79_stringLessThanOrEqualToTen = _out3
  } else {
    _79_stringLessThanOrEqualToTen = _dafny.SeqOfString("leq10")
  }
  var _80_overrideMyBlob bool
  _ = _80_overrideMyBlob
  _80_overrideMyBlob = (overrideToInvalidInput).Contains(_dafny.SeqOfString("myBlob"))
  var _81_myBlob _dafny.Sequence = _dafny.EmptySeq
  _ = _81_myBlob
  if (_80_overrideMyBlob) {
    var _out4 _dafny.Sequence
    _ = _out4
    _out4 = Companion_Default___.InvalidMyBlob()
    _81_myBlob = _out4
  } else {
    _81_myBlob = _dafny.SeqOf(uint8(0), uint8(1), uint8(0), uint8(1))
  }
  var _82_nonEmptyBlob _dafny.Sequence
  _ = _82_nonEmptyBlob
  _82_nonEmptyBlob = _dafny.SeqOf(uint8(0), uint8(1), uint8(0), uint8(1))
  var _83_BlobLessThanOrEqualToTen _dafny.Sequence
  _ = _83_BlobLessThanOrEqualToTen
  _83_BlobLessThanOrEqualToTen = _dafny.SeqOf(uint8(0), uint8(1), uint8(0), uint8(1))
  var _84_myList _dafny.Sequence
  _ = _84_myList
  _84_myList = _dafny.SeqOf(_dafny.SeqOfString("00"), _dafny.SeqOfString("11"))
  var _85_nonEmptyList _dafny.Sequence
  _ = _85_nonEmptyList
  _85_nonEmptyList = _dafny.SeqOf(_dafny.SeqOfString("00"), _dafny.SeqOfString("11"))
  var _86_listLessThanOrEqualToTen _dafny.Sequence
  _ = _86_listLessThanOrEqualToTen
  _86_listLessThanOrEqualToTen = _dafny.SeqOf(_dafny.SeqOfString("00"), _dafny.SeqOfString("11"))
  var _87_myMap _dafny.Map
  _ = _87_myMap
  _87_myMap = _dafny.NewMapBuilder().Add(_dafny.SeqOfString("0"), _dafny.SeqOfString("1")).Add(_dafny.SeqOfString("2"), _dafny.SeqOfString("3")).ToMap()
  var _88_nonEmptyMap _dafny.Map
  _ = _88_nonEmptyMap
  _88_nonEmptyMap = _dafny.NewMapBuilder().Add(_dafny.SeqOfString("0"), _dafny.SeqOfString("1")).Add(_dafny.SeqOfString("2"), _dafny.SeqOfString("3")).ToMap()
  var _89_mapLessThanOrEqualToTen _dafny.Map
  _ = _89_mapLessThanOrEqualToTen
  _89_mapLessThanOrEqualToTen = _dafny.NewMapBuilder().Add(_dafny.SeqOfString("0"), _dafny.SeqOfString("1")).Add(_dafny.SeqOfString("2"), _dafny.SeqOfString("3")).ToMap()
  var _90_alphabetic _dafny.Sequence
  _ = _90_alphabetic
  _90_alphabetic = _dafny.SeqOfString("alphabetic")
  var _91_oneToTen int32
  _ = _91_oneToTen
  _91_oneToTen = int32(3)
  var _92_greaterThanOne int32
  _ = _92_greaterThanOne
  _92_greaterThanOne = int32(2)
  var _93_lessThanTen int32
  _ = _93_lessThanTen
  _93_lessThanTen = int32(3)
  var _94_myUniqueList _dafny.Sequence
  _ = _94_myUniqueList
  _94_myUniqueList = _dafny.SeqOf(_dafny.SeqOfString("one"), _dafny.SeqOfString("two"))
  var _95_myComplexUniqueList _dafny.Sequence
  _ = _95_myComplexUniqueList
  _95_myComplexUniqueList = _dafny.SeqOf(simple.constraints.internaldafny.types.Companion_ComplexListElement_.Create_ComplexListElement_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("one")), Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf(uint8(1), uint8(1)))), simple.constraints.internaldafny.types.Companion_ComplexListElement_.Create_ComplexListElement_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("two")), Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf(uint8(2), uint8(2)))))
  var _96_input simple.constraints.internaldafny.types.GetConstraintsInput
  _ = _96_input
  _96_input = simple.constraints.internaldafny.types.Companion_GetConstraintsInput_.Create_GetConstraintsInput_(Wrappers.Companion_Option_.Create_Some_(_75_myString), Wrappers.Companion_Option_.Create_Some_(_77_nonEmptyString), Wrappers.Companion_Option_.Create_Some_(_79_stringLessThanOrEqualToTen), Wrappers.Companion_Option_.Create_Some_(_81_myBlob), Wrappers.Companion_Option_.Create_Some_(_82_nonEmptyBlob), Wrappers.Companion_Option_.Create_Some_(_83_BlobLessThanOrEqualToTen), Wrappers.Companion_Option_.Create_Some_(_84_myList), Wrappers.Companion_Option_.Create_Some_(_85_nonEmptyList), Wrappers.Companion_Option_.Create_Some_(_86_listLessThanOrEqualToTen), Wrappers.Companion_Option_.Create_Some_(_87_myMap), Wrappers.Companion_Option_.Create_Some_(_88_nonEmptyMap), Wrappers.Companion_Option_.Create_Some_(_89_mapLessThanOrEqualToTen), Wrappers.Companion_Option_.Create_Some_(_90_alphabetic), Wrappers.Companion_Option_.Create_Some_(_91_oneToTen), Wrappers.Companion_Option_.Create_Some_(_92_greaterThanOne), Wrappers.Companion_Option_.Create_Some_(_93_lessThanTen), Wrappers.Companion_Option_.Create_Some_(_94_myUniqueList), Wrappers.Companion_Option_.Create_Some_(_95_myComplexUniqueList), Wrappers.Companion_Option_.Create_Some_(Companion_Default___.PROVIDER__ID()), Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOf(Companion_Default___.PROVIDER__ID(), Companion_Default___.PROVIDER__ID())))
  output = _96_input
  return output
  return output
}
func (_static *CompanionStruct_Default___) InvalidLessThanTenInput() int32 {
  var invalid int32 = int32(0)
  _ = invalid
  var _97_invalidLessThanTenInput int32
  _ = _97_invalidLessThanTenInput
  _97_invalidLessThanTenInput = int32(12)
  var _98_invalidLessThanTen int32
  _ = _98_invalidLessThanTen
  _98_invalidLessThanTen = _97_invalidLessThanTenInput
  invalid = _98_invalidLessThanTen
  return invalid
  return invalid
}
func (_static *CompanionStruct_Default___) InvalidMyStringInput() _dafny.Sequence {
  var invalid _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = invalid
  var _99_invalidMyStringInput _dafny.Sequence
  _ = _99_invalidMyStringInput
  _99_invalidMyStringInput = _dafny.SeqOfString("thisislongerthan10characters")
  var _100_invalidMyString _dafny.Sequence
  _ = _100_invalidMyString
  _100_invalidMyString = _99_invalidMyStringInput
  invalid = _100_invalidMyString
  return invalid
  return invalid
}
func (_static *CompanionStruct_Default___) InvalidNonEmptyStringInput() _dafny.Sequence {
  var invalid _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = invalid
  var _101_invalidNonEmptyStringInput _dafny.Sequence
  _ = _101_invalidNonEmptyStringInput
  _101_invalidNonEmptyStringInput = _dafny.SeqOfString("")
  var _102_invalidNonEmptyString _dafny.Sequence
  _ = _102_invalidNonEmptyString
  _102_invalidNonEmptyString = _101_invalidNonEmptyStringInput
  invalid = _102_invalidNonEmptyString
  return invalid
  return invalid
}
func (_static *CompanionStruct_Default___) InvalidStringLessThanOrEqualToTen() _dafny.Sequence {
  var invalid _dafny.Sequence = _dafny.EmptySeq.SetString()
  _ = invalid
  var _103_invalidStringLessThanOrEqualToTenInput _dafny.Sequence
  _ = _103_invalidStringLessThanOrEqualToTenInput
  _103_invalidStringLessThanOrEqualToTenInput = _dafny.SeqOfString("")
  var _104_invalidStringLessThanOrEqualToTen _dafny.Sequence
  _ = _104_invalidStringLessThanOrEqualToTen
  _104_invalidStringLessThanOrEqualToTen = _103_invalidStringLessThanOrEqualToTenInput
  invalid = _104_invalidStringLessThanOrEqualToTen
  return invalid
  return invalid
}
func (_static *CompanionStruct_Default___) InvalidMyBlob() _dafny.Sequence {
  var invalid _dafny.Sequence = _dafny.EmptySeq
  _ = invalid
  var _105_invalidMyBlobInput _dafny.Sequence
  _ = _105_invalidMyBlobInput
  _105_invalidMyBlobInput = _dafny.SeqOf()
  var _106_invalidMyBlob _dafny.Sequence
  _ = _106_invalidMyBlob
  _106_invalidMyBlob = _105_invalidMyBlobInput
  invalid = _106_invalidMyBlob
  return invalid
  return invalid
}
func (_static *CompanionStruct_Default___) PROVIDER__ID() _dafny.Sequence {
  var _107_s _dafny.Sequence = _dafny.SeqOf(uint8(97), uint8(119), uint8(115), uint8(45), uint8(107), uint8(109), uint8(115))
  _ = _107_s
  return _107_s
}
// End of class Default__
