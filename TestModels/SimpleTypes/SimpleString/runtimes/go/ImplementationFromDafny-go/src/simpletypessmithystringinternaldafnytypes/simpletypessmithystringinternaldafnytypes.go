// Package simpletypessmithystringinternaldafnytypes
// Dafny module simpletypessmithystringinternaldafnytypes compiled into Go

package simpletypessmithystringinternaldafnytypes

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Wrappers "Wrappers"
  StandardLibrary_mUInt "StandardLibrary_mUInt"
  StandardLibrary "StandardLibrary"
  UTF8 "UTF8"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__

type Dummy__ struct{}



// Definition of datatype DafnyCallEvent
type DafnyCallEvent struct {
  Data_DafnyCallEvent_
}

func (_this DafnyCallEvent) Get() Data_DafnyCallEvent_ {
  return _this.Data_DafnyCallEvent_
}

type Data_DafnyCallEvent_ interface {
  isDafnyCallEvent()
}

type CompanionStruct_DafnyCallEvent_ struct {
}
var Companion_DafnyCallEvent_ = CompanionStruct_DafnyCallEvent_ {
}

type DafnyCallEvent_DafnyCallEvent struct {
  Input interface{}
  Output interface{}
}

func (DafnyCallEvent_DafnyCallEvent) isDafnyCallEvent() {}

func (CompanionStruct_DafnyCallEvent_) Create_DafnyCallEvent_(Input interface{}, Output interface{}) DafnyCallEvent {
  return DafnyCallEvent{DafnyCallEvent_DafnyCallEvent{Input, Output}}
}

func (_this DafnyCallEvent) Is_DafnyCallEvent() bool {
  _, ok := _this.Get().(DafnyCallEvent_DafnyCallEvent)
  return ok
}

func (CompanionStruct_DafnyCallEvent_) Default(_default_I interface{}, _default_O interface{}) DafnyCallEvent {
  return Companion_DafnyCallEvent_.Create_DafnyCallEvent_(_default_I, _default_O)
}

func (_this DafnyCallEvent) Dtor_input() interface{} {
  return _this.Get().(DafnyCallEvent_DafnyCallEvent).Input
}

func (_this DafnyCallEvent) Dtor_output() interface{} {
  return _this.Get().(DafnyCallEvent_DafnyCallEvent).Output
}

func (_this DafnyCallEvent) String() string {
  switch data := _this.Get().(type) {
    case nil: return "null"
    case DafnyCallEvent_DafnyCallEvent: {
      return "SimpleTypesSmithyStringTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this DafnyCallEvent) Equals(other DafnyCallEvent) bool {
  switch data1 := _this.Get().(type) {
    case DafnyCallEvent_DafnyCallEvent: {
      data2, ok := other.Get().(DafnyCallEvent_DafnyCallEvent)
      return ok && _dafny.AreEqual(data1.Input, data2.Input) && _dafny.AreEqual(data1.Output, data2.Output)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this DafnyCallEvent) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(DafnyCallEvent)
  return ok && _this.Equals(typed)
}

func Type_DafnyCallEvent_(Type_I_ _dafny.TypeDescriptor, Type_O_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_DafnyCallEvent_{Type_I_, Type_O_}
}

type type_DafnyCallEvent_ struct {
  Type_I_ _dafny.TypeDescriptor
  Type_O_ _dafny.TypeDescriptor
}

func (_this type_DafnyCallEvent_) Default() interface{} {
  Type_I_ := _this.Type_I_
  _ = Type_I_
  Type_O_ := _this.Type_O_
  _ = Type_O_
  return Companion_DafnyCallEvent_.Default(Type_I_.Default(), Type_O_.Default());
}

func (_this type_DafnyCallEvent_) String() string {
  return "simpletypessmithystringinternaldafnytypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype GetStringInput
type GetStringInput struct {
  Data_GetStringInput_
}

func (_this GetStringInput) Get() Data_GetStringInput_ {
  return _this.Data_GetStringInput_
}

type Data_GetStringInput_ interface {
  isGetStringInput()
}

type CompanionStruct_GetStringInput_ struct {
}
var Companion_GetStringInput_ = CompanionStruct_GetStringInput_ {
}

type GetStringInput_GetStringInput struct {
  Value Wrappers.Option
}

func (GetStringInput_GetStringInput) isGetStringInput() {}

func (CompanionStruct_GetStringInput_) Create_GetStringInput_(Value Wrappers.Option) GetStringInput {
  return GetStringInput{GetStringInput_GetStringInput{Value}}
}

func (_this GetStringInput) Is_GetStringInput() bool {
  _, ok := _this.Get().(GetStringInput_GetStringInput)
  return ok
}

func (CompanionStruct_GetStringInput_) Default() GetStringInput {
  return Companion_GetStringInput_.Create_GetStringInput_(Wrappers.Companion_Option_.Default())
}

func (_this GetStringInput) Dtor_value() Wrappers.Option {
  return _this.Get().(GetStringInput_GetStringInput).Value
}

func (_this GetStringInput) String() string {
  switch data := _this.Get().(type) {
    case nil: return "null"
    case GetStringInput_GetStringInput: {
      return "SimpleTypesSmithyStringTypes.GetStringInput.GetStringInput" + "(" + _dafny.String(data.Value) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this GetStringInput) Equals(other GetStringInput) bool {
  switch data1 := _this.Get().(type) {
    case GetStringInput_GetStringInput: {
      data2, ok := other.Get().(GetStringInput_GetStringInput)
      return ok && data1.Value.Equals(data2.Value)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this GetStringInput) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(GetStringInput)
  return ok && _this.Equals(typed)
}

func Type_GetStringInput_() _dafny.TypeDescriptor {
  return type_GetStringInput_{}
}

type type_GetStringInput_ struct {
}

func (_this type_GetStringInput_) Default() interface{} {
  return Companion_GetStringInput_.Default();
}

func (_this type_GetStringInput_) String() string {
  return "simpletypessmithystringinternaldafnytypes.GetStringInput"
}
func (_this GetStringInput) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = GetStringInput{}

// End of datatype GetStringInput

// Definition of datatype GetStringOutput
type GetStringOutput struct {
  Data_GetStringOutput_
}

func (_this GetStringOutput) Get() Data_GetStringOutput_ {
  return _this.Data_GetStringOutput_
}

type Data_GetStringOutput_ interface {
  isGetStringOutput()
}

type CompanionStruct_GetStringOutput_ struct {
}
var Companion_GetStringOutput_ = CompanionStruct_GetStringOutput_ {
}

type GetStringOutput_GetStringOutput struct {
  Value Wrappers.Option
}

func (GetStringOutput_GetStringOutput) isGetStringOutput() {}

func (CompanionStruct_GetStringOutput_) Create_GetStringOutput_(Value Wrappers.Option) GetStringOutput {
  return GetStringOutput{GetStringOutput_GetStringOutput{Value}}
}

func (_this GetStringOutput) Is_GetStringOutput() bool {
  _, ok := _this.Get().(GetStringOutput_GetStringOutput)
  return ok
}

func (CompanionStruct_GetStringOutput_) Default() GetStringOutput {
  return Companion_GetStringOutput_.Create_GetStringOutput_(Wrappers.Companion_Option_.Default())
}

func (_this GetStringOutput) Dtor_value() Wrappers.Option {
  return _this.Get().(GetStringOutput_GetStringOutput).Value
}

func (_this GetStringOutput) String() string {
  switch data := _this.Get().(type) {
    case nil: return "null"
    case GetStringOutput_GetStringOutput: {
      return "SimpleTypesSmithyStringTypes.GetStringOutput.GetStringOutput" + "(" + _dafny.String(data.Value) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this GetStringOutput) Equals(other GetStringOutput) bool {
  switch data1 := _this.Get().(type) {
    case GetStringOutput_GetStringOutput: {
      data2, ok := other.Get().(GetStringOutput_GetStringOutput)
      return ok && data1.Value.Equals(data2.Value)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this GetStringOutput) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(GetStringOutput)
  return ok && _this.Equals(typed)
}

func Type_GetStringOutput_() _dafny.TypeDescriptor {
  return type_GetStringOutput_{}
}

type type_GetStringOutput_ struct {
}

func (_this type_GetStringOutput_) Default() interface{} {
  return Companion_GetStringOutput_.Default();
}

func (_this type_GetStringOutput_) String() string {
  return "simpletypessmithystringinternaldafnytypes.GetStringOutput"
}
func (_this GetStringOutput) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = GetStringOutput{}

// End of datatype GetStringOutput

// Definition of datatype SimpleStringConfig
type SimpleStringConfig struct {
  Data_SimpleStringConfig_
}

func (_this SimpleStringConfig) Get() Data_SimpleStringConfig_ {
  return _this.Data_SimpleStringConfig_
}

type Data_SimpleStringConfig_ interface {
  isSimpleStringConfig()
}

type CompanionStruct_SimpleStringConfig_ struct {
}
var Companion_SimpleStringConfig_ = CompanionStruct_SimpleStringConfig_ {
}

type SimpleStringConfig_SimpleStringConfig struct {
}

func (SimpleStringConfig_SimpleStringConfig) isSimpleStringConfig() {}

func (CompanionStruct_SimpleStringConfig_) Create_SimpleStringConfig_() SimpleStringConfig {
  return SimpleStringConfig{SimpleStringConfig_SimpleStringConfig{}}
}

func (_this SimpleStringConfig) Is_SimpleStringConfig() bool {
  _, ok := _this.Get().(SimpleStringConfig_SimpleStringConfig)
  return ok
}

func (CompanionStruct_SimpleStringConfig_) Default() SimpleStringConfig {
  return Companion_SimpleStringConfig_.Create_SimpleStringConfig_()
}

func (_ CompanionStruct_SimpleStringConfig_) AllSingletonConstructors() _dafny.Iterator {
  i := -1
  return func() (interface{}, bool) {
    i++
    switch i {
      case 0: return Companion_SimpleStringConfig_.Create_SimpleStringConfig_(), true
      default: return SimpleStringConfig{}, false
    }
  }
}

func (_this SimpleStringConfig) String() string {
  switch _this.Get().(type) {
    case nil: return "null"
    case SimpleStringConfig_SimpleStringConfig: {
      return "SimpleTypesSmithyStringTypes.SimpleStringConfig.SimpleStringConfig"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this SimpleStringConfig) Equals(other SimpleStringConfig) bool {
  switch _this.Get().(type) {
    case SimpleStringConfig_SimpleStringConfig: {
      _, ok := other.Get().(SimpleStringConfig_SimpleStringConfig)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this SimpleStringConfig) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(SimpleStringConfig)
  return ok && _this.Equals(typed)
}

func Type_SimpleStringConfig_() _dafny.TypeDescriptor {
  return type_SimpleStringConfig_{}
}

type type_SimpleStringConfig_ struct {
}

func (_this type_SimpleStringConfig_) Default() interface{} {
  return Companion_SimpleStringConfig_.Default();
}

func (_this type_SimpleStringConfig_) String() string {
  return "simpletypessmithystringinternaldafnytypes.SimpleStringConfig"
}
func (_this SimpleStringConfig) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = SimpleStringConfig{}

// End of datatype SimpleStringConfig

// Definition of class ISimpleTypesStringClientCallHistory
type ISimpleTypesStringClientCallHistory struct {
  dummy byte
}

func New_ISimpleTypesStringClientCallHistory_() *ISimpleTypesStringClientCallHistory {
  _this := ISimpleTypesStringClientCallHistory{}

  return &_this
}

type CompanionStruct_ISimpleTypesStringClientCallHistory_ struct {
}
var Companion_ISimpleTypesStringClientCallHistory_ = CompanionStruct_ISimpleTypesStringClientCallHistory_ {
}

func (_this *ISimpleTypesStringClientCallHistory) Equals(other *ISimpleTypesStringClientCallHistory) bool {
  return _this == other
}

func (_this *ISimpleTypesStringClientCallHistory) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*ISimpleTypesStringClientCallHistory)
  return ok && _this.Equals(other)
}

func (*ISimpleTypesStringClientCallHistory) String() string {
  return "simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClientCallHistory"
}

func Type_ISimpleTypesStringClientCallHistory_() _dafny.TypeDescriptor {
  return type_ISimpleTypesStringClientCallHistory_{}
}

type type_ISimpleTypesStringClientCallHistory_ struct {
}

func (_this type_ISimpleTypesStringClientCallHistory_) Default() interface{} {
  return (*ISimpleTypesStringClientCallHistory)(nil)
}

func (_this type_ISimpleTypesStringClientCallHistory_) String() string {
  return "simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClientCallHistory"
}
func (_this *ISimpleTypesStringClientCallHistory) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &ISimpleTypesStringClientCallHistory{}

// End of class ISimpleTypesStringClientCallHistory

// Definition of trait ISimpleTypesStringClient
type ISimpleTypesStringClient interface {
  String() string
  GetString(input GetStringInput) Wrappers.Result
  GetStringSingleValue(input GetStringInput) Wrappers.Result
  GetStringUTF8(input GetStringInput) Wrappers.Result
}
type CompanionStruct_ISimpleTypesStringClient_ struct {
  TraitID_ *_dafny.TraitID
}
var Companion_ISimpleTypesStringClient_ = CompanionStruct_ISimpleTypesStringClient_ {
  TraitID_: &_dafny.TraitID{},
}
func (CompanionStruct_ISimpleTypesStringClient_) CastTo_(x interface{}) ISimpleTypesStringClient {
  var t ISimpleTypesStringClient
  t, _ = x.(ISimpleTypesStringClient)
  return t
}
// End of trait ISimpleTypesStringClient

// Definition of datatype Error
type Error struct {
  Data_Error_
}

func (_this Error) Get() Data_Error_ {
  return _this.Data_Error_
}

type Data_Error_ interface {
  isError()
}

type CompanionStruct_Error_ struct {
}
var Companion_Error_ = CompanionStruct_Error_ {
}

type Error_CollectionOfErrors struct {
  List _dafny.Sequence
  Message _dafny.Sequence
}

func (Error_CollectionOfErrors) isError() {}

func (CompanionStruct_Error_) Create_CollectionOfErrors_(List _dafny.Sequence, Message _dafny.Sequence) Error {
  return Error{Error_CollectionOfErrors{List, Message}}
}

func (_this Error) Is_CollectionOfErrors() bool {
  _, ok := _this.Get().(Error_CollectionOfErrors)
  return ok
}

type Error_Opaque struct {
  Obj interface{}
}

func (Error_Opaque) isError() {}

func (CompanionStruct_Error_) Create_Opaque_(Obj interface{}) Error {
  return Error{Error_Opaque{Obj}}
}

func (_this Error) Is_Opaque() bool {
  _, ok := _this.Get().(Error_Opaque)
  return ok
}

func (CompanionStruct_Error_) Default() Error {
  return Companion_Error_.Create_CollectionOfErrors_(_dafny.EmptySeq, _dafny.EmptySeq.SetString())
}

func (_this Error) Dtor_list() _dafny.Sequence {
  return _this.Get().(Error_CollectionOfErrors).List
}

func (_this Error) Dtor_message() _dafny.Sequence {
  return _this.Get().(Error_CollectionOfErrors).Message
}

func (_this Error) Dtor_obj() interface{} {
  return _this.Get().(Error_Opaque).Obj
}

func (_this Error) String() string {
  switch data := _this.Get().(type) {
    case nil: return "null"
    case Error_CollectionOfErrors: {
      return "SimpleTypesSmithyStringTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + _dafny.String(data.Message) + ")"
    }
    case Error_Opaque: {
      return "SimpleTypesSmithyStringTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Error) Equals(other Error) bool {
  switch data1 := _this.Get().(type) {
    case Error_CollectionOfErrors: {
      data2, ok := other.Get().(Error_CollectionOfErrors)
      return ok && data1.List.Equals(data2.List) && data1.Message.Equals(data2.Message)
    }
    case Error_Opaque: {
      data2, ok := other.Get().(Error_Opaque)
      return ok && _dafny.AreEqual(data1.Obj, data2.Obj)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Error) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Error)
  return ok && _this.Equals(typed)
}

func Type_Error_() _dafny.TypeDescriptor {
  return type_Error_{}
}

type type_Error_ struct {
}

func (_this type_Error_) Default() interface{} {
  return Companion_Error_.Default();
}

func (_this type_Error_) String() string {
  return "simpletypessmithystringinternaldafnytypes.Error"
}
func (_this Error) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Error{}

// End of datatype Error

// Definition of class OpaqueError
type OpaqueError struct {
}

func New_OpaqueError_() *OpaqueError {
  _this := OpaqueError{}

  return &_this
}

type CompanionStruct_OpaqueError_ struct {
}
var Companion_OpaqueError_ = CompanionStruct_OpaqueError_ {
}

func (*OpaqueError) String() string {
  return "simpletypessmithystringinternaldafnytypes.OpaqueError"
}
// End of class OpaqueError

func Type_OpaqueError_() _dafny.TypeDescriptor {
  return type_OpaqueError_{}
}

type type_OpaqueError_ struct {
}

func (_this type_OpaqueError_) Default() interface{} {
  return Companion_Error_.Default()
}

func (_this type_OpaqueError_) String() string {
  return "simpletypessmithystringinternaldafnytypes.OpaqueError"
}
