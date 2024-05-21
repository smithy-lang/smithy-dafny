// Package SimpleStringImplTest
// Dafny module SimpleStringImplTest compiled into Go

package SimpleStringImplTest

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Wrappers "Wrappers"
  StandardLibrary_mUInt "StandardLibrary_mUInt"
  StandardLibrary "StandardLibrary"
  UTF8 "UTF8"
  simpletypessmithystringinternaldafnytypes "simpletypessmithystringinternaldafnytypes"
  SimpleStringImpl "SimpleStringImpl"
  simpletypessmithystringinternaldafny "simpletypessmithystringinternaldafny"
  simpletypessmithystringinternaldafnywrapped "simpletypessmithystringinternaldafnywrapped"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleStringImpl.Dummy__

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
  return "SimpleStringImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetString() {
  var _76_client *simpletypessmithystringinternaldafny.SimpleStringClient
  _ = _76_client
  var _77_valueOrError0 Wrappers.Result = Wrappers.Result{}
  _ = _77_valueOrError0
  var _out3 Wrappers.Result
  _ = _out3
  _out3 = simpletypessmithystringinternaldafny.Companion_Default___.SimpleString(simpletypessmithystringinternaldafny.Companion_Default___.DefaultSimpleStringConfig())
  _77_valueOrError0 = _out3
  if (!(!((_77_valueOrError0).IsFailure()))) {
    panic("test/SimpleStringImplTest.dfy(10,19): " + (_77_valueOrError0).String())
  }
  _76_client = (_77_valueOrError0).Extract().(*simpletypessmithystringinternaldafny.SimpleStringClient)
  Companion_Default___.TestGetString(_76_client)
  Companion_Default___.TestGetStringSingleValue(_76_client)
  Companion_Default___.TestGetStringUTF8(_76_client)
}
func (_static *CompanionStruct_Default___) TestGetString(client simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClient) {
  var _78_ret simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _78_ret
  var _79_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = _79_valueOrError0
  var _out4 Wrappers.Result
  _ = _out4
  _out4 = (client).GetString(simpletypessmithystringinternaldafnytypes.Companion_GetStringInput_.Create_GetStringInput_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("TEST_SIMPLE_STRING_VALUE"))))
  _79_valueOrError0 = _out4
  if (!(!((_79_valueOrError0).IsFailure()))) {
    panic("test/SimpleStringImplTest.dfy(21,16): " + (_79_valueOrError0).String())
  }
  _78_ret = (_79_valueOrError0).Extract().(simpletypessmithystringinternaldafnytypes.GetStringOutput)
  if (!(_dafny.Companion_Sequence_.Equal(((_78_ret).Dtor_value()).UnwrapOr(_dafny.SeqOfString("")).(_dafny.Sequence), _dafny.SeqOfString("TEST_SIMPLE_STRING_VALUE")))) {
    panic("test/SimpleStringImplTest.dfy(22,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  _dafny.Print(_78_ret)
}
func (_static *CompanionStruct_Default___) TestGetStringSingleValue(client simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClient) {
  var _80_ret simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _80_ret
  var _81_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = _81_valueOrError0
  var _out5 Wrappers.Result
  _ = _out5
  _out5 = (client).GetStringSingleValue(simpletypessmithystringinternaldafnytypes.Companion_GetStringInput_.Create_GetStringInput_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("TEST_SIMPLE_STRING_SINGLE_VALUE"))))
  _81_valueOrError0 = _out5
  if (!(!((_81_valueOrError0).IsFailure()))) {
    panic("test/SimpleStringImplTest.dfy(30,16): " + (_81_valueOrError0).String())
  }
  _80_ret = (_81_valueOrError0).Extract().(simpletypessmithystringinternaldafnytypes.GetStringOutput)
  if (!(_dafny.Companion_Sequence_.Equal(((_80_ret).Dtor_value()).UnwrapOr(_dafny.SeqOfString("")).(_dafny.Sequence), _dafny.SeqOfString("TEST_SIMPLE_STRING_SINGLE_VALUE")))) {
    panic("test/SimpleStringImplTest.dfy(31,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  _dafny.Print(_80_ret)
}
func (_static *CompanionStruct_Default___) TestGetStringUTF8(client simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClient) {
  var _82_utf8EncodedString _dafny.Sequence
  _ = _82_utf8EncodedString
  _82_utf8EncodedString = _dafny.SeqOfChars(2309, 2344, 2366, 2352)
  var _83_ret simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _83_ret
  var _84_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = _84_valueOrError0
  var _out6 Wrappers.Result
  _ = _out6
  _out6 = (client).GetStringUTF8(simpletypessmithystringinternaldafnytypes.Companion_GetStringInput_.Create_GetStringInput_(Wrappers.Companion_Option_.Create_Some_(_82_utf8EncodedString)))
  _84_valueOrError0 = _out6
  if (!(!((_84_valueOrError0).IsFailure()))) {
    panic("test/SimpleStringImplTest.dfy(41,16): " + (_84_valueOrError0).String())
  }
  _83_ret = (_84_valueOrError0).Extract().(simpletypessmithystringinternaldafnytypes.GetStringOutput)
  if (!(_dafny.Companion_Sequence_.Equal(((_83_ret).Dtor_value()).UnwrapOr(_dafny.SeqOfString("")).(_dafny.Sequence), _82_utf8EncodedString))) {
    panic("test/SimpleStringImplTest.dfy(42,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  _dafny.Print(_83_ret)
}
// End of class Default__
