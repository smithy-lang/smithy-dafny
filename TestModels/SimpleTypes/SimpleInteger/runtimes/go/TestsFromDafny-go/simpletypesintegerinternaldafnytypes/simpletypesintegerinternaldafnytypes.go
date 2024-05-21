// Package simpletypesintegerinternaldafnytypes
// Dafny module simpletypesintegerinternaldafnytypes compiled into Go

package simpletypesintegerinternaldafnytypes

import (
	os "os"

	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__

type Dummy__ struct{}

// Definition of datatype DafnyCallEvent
type DafnyCallEvent struct {
	Data_DafnyCallEvent_
}

func (_this DafnyCallEvent) Get_() Data_DafnyCallEvent_ {
	return _this.Data_DafnyCallEvent_
}

type Data_DafnyCallEvent_ interface {
	isDafnyCallEvent()
}

type CompanionStruct_DafnyCallEvent_ struct {
}

var Companion_DafnyCallEvent_ = CompanionStruct_DafnyCallEvent_{}

type DafnyCallEvent_DafnyCallEvent struct {
	Input  interface{}
	Output interface{}
}

func (DafnyCallEvent_DafnyCallEvent) isDafnyCallEvent() {}

func (CompanionStruct_DafnyCallEvent_) Create_DafnyCallEvent_(Input interface{}, Output interface{}) DafnyCallEvent {
	return DafnyCallEvent{DafnyCallEvent_DafnyCallEvent{Input, Output}}
}

func (_this DafnyCallEvent) Is_DafnyCallEvent() bool {
	_, ok := _this.Get_().(DafnyCallEvent_DafnyCallEvent)
	return ok
}

func (CompanionStruct_DafnyCallEvent_) Default(_default_I interface{}, _default_O interface{}) DafnyCallEvent {
	return Companion_DafnyCallEvent_.Create_DafnyCallEvent_(_default_I, _default_O)
}

func (_this DafnyCallEvent) Dtor_input() interface{} {
	return _this.Get_().(DafnyCallEvent_DafnyCallEvent).Input
}

func (_this DafnyCallEvent) Dtor_output() interface{} {
	return _this.Get_().(DafnyCallEvent_DafnyCallEvent).Output
}

func (_this DafnyCallEvent) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case DafnyCallEvent_DafnyCallEvent:
		{
			return "SimpleTypesIntegerTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this DafnyCallEvent) Equals(other DafnyCallEvent) bool {
	switch data1 := _this.Get_().(type) {
	case DafnyCallEvent_DafnyCallEvent:
		{
			data2, ok := other.Get_().(DafnyCallEvent_DafnyCallEvent)
			return ok && _dafny.AreEqual(data1.Input, data2.Input) && _dafny.AreEqual(data1.Output, data2.Output)
		}
	default:
		{
			return false // unexpected
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
	return Companion_DafnyCallEvent_.Default(Type_I_.Default(), Type_O_.Default())
}

func (_this type_DafnyCallEvent_) String() string {
	return "simpletypesintegerinternaldafnytypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype GetIntegerInput
type GetIntegerInput struct {
	Data_GetIntegerInput_
}

func (_this GetIntegerInput) Get_() Data_GetIntegerInput_ {
	return _this.Data_GetIntegerInput_
}

type Data_GetIntegerInput_ interface {
	isGetIntegerInput()
}

type CompanionStruct_GetIntegerInput_ struct {
}

var Companion_GetIntegerInput_ = CompanionStruct_GetIntegerInput_{}

type GetIntegerInput_GetIntegerInput struct {
	Value Wrappers.Option
}

func (GetIntegerInput_GetIntegerInput) isGetIntegerInput() {}

func (CompanionStruct_GetIntegerInput_) Create_GetIntegerInput_(Value Wrappers.Option) GetIntegerInput {
	return GetIntegerInput{GetIntegerInput_GetIntegerInput{Value}}
}

func (_this GetIntegerInput) Is_GetIntegerInput() bool {
	_, ok := _this.Get_().(GetIntegerInput_GetIntegerInput)
	return ok
}

func (CompanionStruct_GetIntegerInput_) Default() GetIntegerInput {
	return Companion_GetIntegerInput_.Create_GetIntegerInput_(Wrappers.Companion_Option_.Default())
}

func (_this GetIntegerInput) Dtor_value() Wrappers.Option {
	return _this.Get_().(GetIntegerInput_GetIntegerInput).Value
}

func (_this GetIntegerInput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetIntegerInput_GetIntegerInput:
		{
			return "SimpleTypesIntegerTypes.GetIntegerInput.GetIntegerInput" + "(" + _dafny.String(data.Value) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetIntegerInput) Equals(other GetIntegerInput) bool {
	switch data1 := _this.Get_().(type) {
	case GetIntegerInput_GetIntegerInput:
		{
			data2, ok := other.Get_().(GetIntegerInput_GetIntegerInput)
			return ok && data1.Value.Equals(data2.Value)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetIntegerInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetIntegerInput)
	return ok && _this.Equals(typed)
}

func Type_GetIntegerInput_() _dafny.TypeDescriptor {
	return type_GetIntegerInput_{}
}

type type_GetIntegerInput_ struct {
}

func (_this type_GetIntegerInput_) Default() interface{} {
	return Companion_GetIntegerInput_.Default()
}

func (_this type_GetIntegerInput_) String() string {
	return "simpletypesintegerinternaldafnytypes.GetIntegerInput"
}
func (_this GetIntegerInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetIntegerInput{}

// End of datatype GetIntegerInput

// Definition of datatype GetIntegerOutput
type GetIntegerOutput struct {
	Data_GetIntegerOutput_
}

func (_this GetIntegerOutput) Get_() Data_GetIntegerOutput_ {
	return _this.Data_GetIntegerOutput_
}

type Data_GetIntegerOutput_ interface {
	isGetIntegerOutput()
}

type CompanionStruct_GetIntegerOutput_ struct {
}

var Companion_GetIntegerOutput_ = CompanionStruct_GetIntegerOutput_{}

type GetIntegerOutput_GetIntegerOutput struct {
	Value Wrappers.Option
}

func (GetIntegerOutput_GetIntegerOutput) isGetIntegerOutput() {}

func (CompanionStruct_GetIntegerOutput_) Create_GetIntegerOutput_(Value Wrappers.Option) GetIntegerOutput {
	return GetIntegerOutput{GetIntegerOutput_GetIntegerOutput{Value}}
}

func (_this GetIntegerOutput) Is_GetIntegerOutput() bool {
	_, ok := _this.Get_().(GetIntegerOutput_GetIntegerOutput)
	return ok
}

func (CompanionStruct_GetIntegerOutput_) Default() GetIntegerOutput {
	return Companion_GetIntegerOutput_.Create_GetIntegerOutput_(Wrappers.Companion_Option_.Default())
}

func (_this GetIntegerOutput) Dtor_value() Wrappers.Option {
	return _this.Get_().(GetIntegerOutput_GetIntegerOutput).Value
}

func (_this GetIntegerOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetIntegerOutput_GetIntegerOutput:
		{
			return "SimpleTypesIntegerTypes.GetIntegerOutput.GetIntegerOutput" + "(" + _dafny.String(data.Value) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetIntegerOutput) Equals(other GetIntegerOutput) bool {
	switch data1 := _this.Get_().(type) {
	case GetIntegerOutput_GetIntegerOutput:
		{
			data2, ok := other.Get_().(GetIntegerOutput_GetIntegerOutput)
			return ok && data1.Value.Equals(data2.Value)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetIntegerOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetIntegerOutput)
	return ok && _this.Equals(typed)
}

func Type_GetIntegerOutput_() _dafny.TypeDescriptor {
	return type_GetIntegerOutput_{}
}

type type_GetIntegerOutput_ struct {
}

func (_this type_GetIntegerOutput_) Default() interface{} {
	return Companion_GetIntegerOutput_.Default()
}

func (_this type_GetIntegerOutput_) String() string {
	return "simpletypesintegerinternaldafnytypes.GetIntegerOutput"
}
func (_this GetIntegerOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetIntegerOutput{}

// End of datatype GetIntegerOutput

// Definition of datatype SimpleIntegerConfig
type SimpleIntegerConfig struct {
	Data_SimpleIntegerConfig_
}

func (_this SimpleIntegerConfig) Get_() Data_SimpleIntegerConfig_ {
	return _this.Data_SimpleIntegerConfig_
}

type Data_SimpleIntegerConfig_ interface {
	isSimpleIntegerConfig()
}

type CompanionStruct_SimpleIntegerConfig_ struct {
}

var Companion_SimpleIntegerConfig_ = CompanionStruct_SimpleIntegerConfig_{}

type SimpleIntegerConfig_SimpleIntegerConfig struct {
}

func (SimpleIntegerConfig_SimpleIntegerConfig) isSimpleIntegerConfig() {}

func (CompanionStruct_SimpleIntegerConfig_) Create_SimpleIntegerConfig_() SimpleIntegerConfig {
	return SimpleIntegerConfig{SimpleIntegerConfig_SimpleIntegerConfig{}}
}

func (_this SimpleIntegerConfig) Is_SimpleIntegerConfig() bool {
	_, ok := _this.Get_().(SimpleIntegerConfig_SimpleIntegerConfig)
	return ok
}

func (CompanionStruct_SimpleIntegerConfig_) Default() SimpleIntegerConfig {
	return Companion_SimpleIntegerConfig_.Create_SimpleIntegerConfig_()
}

func (_ CompanionStruct_SimpleIntegerConfig_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_SimpleIntegerConfig_.Create_SimpleIntegerConfig_(), true
		default:
			return SimpleIntegerConfig{}, false
		}
	}
}

func (_this SimpleIntegerConfig) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case SimpleIntegerConfig_SimpleIntegerConfig:
		{
			return "SimpleTypesIntegerTypes.SimpleIntegerConfig.SimpleIntegerConfig"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this SimpleIntegerConfig) Equals(other SimpleIntegerConfig) bool {
	switch _this.Get_().(type) {
	case SimpleIntegerConfig_SimpleIntegerConfig:
		{
			_, ok := other.Get_().(SimpleIntegerConfig_SimpleIntegerConfig)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this SimpleIntegerConfig) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(SimpleIntegerConfig)
	return ok && _this.Equals(typed)
}

func Type_SimpleIntegerConfig_() _dafny.TypeDescriptor {
	return type_SimpleIntegerConfig_{}
}

type type_SimpleIntegerConfig_ struct {
}

func (_this type_SimpleIntegerConfig_) Default() interface{} {
	return Companion_SimpleIntegerConfig_.Default()
}

func (_this type_SimpleIntegerConfig_) String() string {
	return "simpletypesintegerinternaldafnytypes.SimpleIntegerConfig"
}
func (_this SimpleIntegerConfig) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = SimpleIntegerConfig{}

// End of datatype SimpleIntegerConfig

// Definition of class ISimpleTypesIntegerClientCallHistory
type ISimpleTypesIntegerClientCallHistory struct {
	dummy byte
}

func New_ISimpleTypesIntegerClientCallHistory_() *ISimpleTypesIntegerClientCallHistory {
	_this := ISimpleTypesIntegerClientCallHistory{}

	return &_this
}

type CompanionStruct_ISimpleTypesIntegerClientCallHistory_ struct {
}

var Companion_ISimpleTypesIntegerClientCallHistory_ = CompanionStruct_ISimpleTypesIntegerClientCallHistory_{}

func (_this *ISimpleTypesIntegerClientCallHistory) Equals(other *ISimpleTypesIntegerClientCallHistory) bool {
	return _this == other
}

func (_this *ISimpleTypesIntegerClientCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimpleTypesIntegerClientCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimpleTypesIntegerClientCallHistory) String() string {
	return "simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClientCallHistory"
}

func Type_ISimpleTypesIntegerClientCallHistory_() _dafny.TypeDescriptor {
	return type_ISimpleTypesIntegerClientCallHistory_{}
}

type type_ISimpleTypesIntegerClientCallHistory_ struct {
}

func (_this type_ISimpleTypesIntegerClientCallHistory_) Default() interface{} {
	return (*ISimpleTypesIntegerClientCallHistory)(nil)
}

func (_this type_ISimpleTypesIntegerClientCallHistory_) String() string {
	return "simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClientCallHistory"
}
func (_this *ISimpleTypesIntegerClientCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimpleTypesIntegerClientCallHistory{}

// End of class ISimpleTypesIntegerClientCallHistory

// Definition of trait ISimpleTypesIntegerClient
type ISimpleTypesIntegerClient interface {
	String() string
	GetInteger(input GetIntegerInput) Wrappers.Result
	GetIntegerKnownValueTest(input GetIntegerInput) Wrappers.Result
}
type CompanionStruct_ISimpleTypesIntegerClient_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimpleTypesIntegerClient_ = CompanionStruct_ISimpleTypesIntegerClient_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimpleTypesIntegerClient_) CastTo_(x interface{}) ISimpleTypesIntegerClient {
	var t ISimpleTypesIntegerClient
	t, _ = x.(ISimpleTypesIntegerClient)
	return t
}

// End of trait ISimpleTypesIntegerClient

// Definition of datatype Error
type Error struct {
	Data_Error_
}

func (_this Error) Get_() Data_Error_ {
	return _this.Data_Error_
}

type Data_Error_ interface {
	isError()
}

type CompanionStruct_Error_ struct {
}

var Companion_Error_ = CompanionStruct_Error_{}

type Error_CollectionOfErrors struct {
	List    _dafny.Sequence
	Message _dafny.Sequence
}

func (Error_CollectionOfErrors) isError() {}

func (CompanionStruct_Error_) Create_CollectionOfErrors_(List _dafny.Sequence, Message _dafny.Sequence) Error {
	return Error{Error_CollectionOfErrors{List, Message}}
}

func (_this Error) Is_CollectionOfErrors() bool {
	_, ok := _this.Get_().(Error_CollectionOfErrors)
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
	_, ok := _this.Get_().(Error_Opaque)
	return ok
}

func (CompanionStruct_Error_) Default() Error {
	return Companion_Error_.Create_CollectionOfErrors_(_dafny.EmptySeq, _dafny.EmptySeq)
}

func (_this Error) Dtor_list() _dafny.Sequence {
	return _this.Get_().(Error_CollectionOfErrors).List
}

func (_this Error) Dtor_message() _dafny.Sequence {
	return _this.Get_().(Error_CollectionOfErrors).Message
}

func (_this Error) Dtor_obj() interface{} {
	return _this.Get_().(Error_Opaque).Obj
}

func (_this Error) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case Error_CollectionOfErrors:
		{
			return "SimpleTypesIntegerTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + data.Message.VerbatimString(true) + ")"
		}
	case Error_Opaque:
		{
			return "SimpleTypesIntegerTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Error) Equals(other Error) bool {
	switch data1 := _this.Get_().(type) {
	case Error_CollectionOfErrors:
		{
			data2, ok := other.Get_().(Error_CollectionOfErrors)
			return ok && data1.List.Equals(data2.List) && data1.Message.Equals(data2.Message)
		}
	case Error_Opaque:
		{
			data2, ok := other.Get_().(Error_Opaque)
			return ok && _dafny.AreEqual(data1.Obj, data2.Obj)
		}
	default:
		{
			return false // unexpected
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
	return Companion_Error_.Default()
}

func (_this type_Error_) String() string {
	return "simpletypesintegerinternaldafnytypes.Error"
}
func (_this Error) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
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

var Companion_OpaqueError_ = CompanionStruct_OpaqueError_{}

func (*OpaqueError) String() string {
	return "simpletypesintegerinternaldafnytypes.OpaqueError"
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
	return "simpletypesintegerinternaldafnytypes.OpaqueError"
}
func (_this *CompanionStruct_OpaqueError_) Is_(__source Error) bool {
	var _77_e Error = (__source)
	_ = _77_e
	return (_77_e).Is_Opaque()
}
