// Package simpletypesbooleaninternaldafnytypes
// Dafny module simpletypesbooleaninternaldafnytypes compiled into Go

package simpletypesbooleaninternaldafnytypes

import (
	StandardLibrary "StandardLibrary"
	StandardLibrary_mUInt "StandardLibrary_mUInt"
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
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
	case nil:
		return "null"
	case DafnyCallEvent_DafnyCallEvent:
		{
			return "SimpleTypesBooleanTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this DafnyCallEvent) Equals(other DafnyCallEvent) bool {
	switch data1 := _this.Get().(type) {
	case DafnyCallEvent_DafnyCallEvent:
		{
			data2, ok := other.Get().(DafnyCallEvent_DafnyCallEvent)
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
	return "simpletypesbooleaninternaldafnytypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype GetBooleanInput
type GetBooleanInput struct {
	Data_GetBooleanInput_
}

func (_this GetBooleanInput) Get() Data_GetBooleanInput_ {
	return _this.Data_GetBooleanInput_
}

type Data_GetBooleanInput_ interface {
	isGetBooleanInput()
}

type CompanionStruct_GetBooleanInput_ struct {
}

var Companion_GetBooleanInput_ = CompanionStruct_GetBooleanInput_{}

type GetBooleanInput_GetBooleanInput struct {
	Value Wrappers.Option
}

func (GetBooleanInput_GetBooleanInput) isGetBooleanInput() {}

func (CompanionStruct_GetBooleanInput_) Create_GetBooleanInput_(Value Wrappers.Option) GetBooleanInput {
	return GetBooleanInput{GetBooleanInput_GetBooleanInput{Value}}
}

func (_this GetBooleanInput) Is_GetBooleanInput() bool {
	_, ok := _this.Get().(GetBooleanInput_GetBooleanInput)
	return ok
}

func (CompanionStruct_GetBooleanInput_) Default() GetBooleanInput {
	return Companion_GetBooleanInput_.Create_GetBooleanInput_(Wrappers.Companion_Option_.Default())
}

func (_this GetBooleanInput) Dtor_value() Wrappers.Option {
	return _this.Get().(GetBooleanInput_GetBooleanInput).Value
}

func (_this GetBooleanInput) String() string {
	switch data := _this.Get().(type) {
	case nil:
		return "null"
	case GetBooleanInput_GetBooleanInput:
		{
			return "SimpleTypesBooleanTypes.GetBooleanInput.GetBooleanInput" + "(" + _dafny.String(data.Value) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetBooleanInput) Equals(other GetBooleanInput) bool {
	switch data1 := _this.Get().(type) {
	case GetBooleanInput_GetBooleanInput:
		{
			data2, ok := other.Get().(GetBooleanInput_GetBooleanInput)
			return ok && data1.Value.Equals(data2.Value)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetBooleanInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetBooleanInput)
	return ok && _this.Equals(typed)
}

func Type_GetBooleanInput_() _dafny.TypeDescriptor {
	return type_GetBooleanInput_{}
}

type type_GetBooleanInput_ struct {
}

func (_this type_GetBooleanInput_) Default() interface{} {
	return Companion_GetBooleanInput_.Default()
}

func (_this type_GetBooleanInput_) String() string {
	return "simpletypesbooleaninternaldafnytypes.GetBooleanInput"
}
func (_this GetBooleanInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetBooleanInput{}

// End of datatype GetBooleanInput

// Definition of datatype GetBooleanOutput
type GetBooleanOutput struct {
	Data_GetBooleanOutput_
}

func (_this GetBooleanOutput) Get() Data_GetBooleanOutput_ {
	return _this.Data_GetBooleanOutput_
}

type Data_GetBooleanOutput_ interface {
	isGetBooleanOutput()
}

type CompanionStruct_GetBooleanOutput_ struct {
}

var Companion_GetBooleanOutput_ = CompanionStruct_GetBooleanOutput_{}

type GetBooleanOutput_GetBooleanOutput struct {
	Value Wrappers.Option
}

func (GetBooleanOutput_GetBooleanOutput) isGetBooleanOutput() {}

func (CompanionStruct_GetBooleanOutput_) Create_GetBooleanOutput_(Value Wrappers.Option) GetBooleanOutput {
	return GetBooleanOutput{GetBooleanOutput_GetBooleanOutput{Value}}
}

func (_this GetBooleanOutput) Is_GetBooleanOutput() bool {
	_, ok := _this.Get().(GetBooleanOutput_GetBooleanOutput)
	return ok
}

func (CompanionStruct_GetBooleanOutput_) Default() GetBooleanOutput {
	return Companion_GetBooleanOutput_.Create_GetBooleanOutput_(Wrappers.Companion_Option_.Default())
}

func (_this GetBooleanOutput) Dtor_value() Wrappers.Option {
	return _this.Get().(GetBooleanOutput_GetBooleanOutput).Value
}

func (_this GetBooleanOutput) String() string {
	switch data := _this.Get().(type) {
	case nil:
		return "null"
	case GetBooleanOutput_GetBooleanOutput:
		{
			return "SimpleTypesBooleanTypes.GetBooleanOutput.GetBooleanOutput" + "(" + _dafny.String(data.Value) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetBooleanOutput) Equals(other GetBooleanOutput) bool {
	switch data1 := _this.Get().(type) {
	case GetBooleanOutput_GetBooleanOutput:
		{
			data2, ok := other.Get().(GetBooleanOutput_GetBooleanOutput)
			return ok && data1.Value.Equals(data2.Value)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetBooleanOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetBooleanOutput)
	return ok && _this.Equals(typed)
}

func Type_GetBooleanOutput_() _dafny.TypeDescriptor {
	return type_GetBooleanOutput_{}
}

type type_GetBooleanOutput_ struct {
}

func (_this type_GetBooleanOutput_) Default() interface{} {
	return Companion_GetBooleanOutput_.Default()
}

func (_this type_GetBooleanOutput_) String() string {
	return "simpletypesbooleaninternaldafnytypes.GetBooleanOutput"
}
func (_this GetBooleanOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetBooleanOutput{}

// End of datatype GetBooleanOutput

// Definition of datatype SimpleBooleanConfig
type SimpleBooleanConfig struct {
	Data_SimpleBooleanConfig_
}

func (_this SimpleBooleanConfig) Get() Data_SimpleBooleanConfig_ {
	return _this.Data_SimpleBooleanConfig_
}

type Data_SimpleBooleanConfig_ interface {
	isSimpleBooleanConfig()
}

type CompanionStruct_SimpleBooleanConfig_ struct {
}

var Companion_SimpleBooleanConfig_ = CompanionStruct_SimpleBooleanConfig_{}

type SimpleBooleanConfig_SimpleBooleanConfig struct {
}

func (SimpleBooleanConfig_SimpleBooleanConfig) isSimpleBooleanConfig() {}

func (CompanionStruct_SimpleBooleanConfig_) Create_SimpleBooleanConfig_() SimpleBooleanConfig {
	return SimpleBooleanConfig{SimpleBooleanConfig_SimpleBooleanConfig{}}
}

func (_this SimpleBooleanConfig) Is_SimpleBooleanConfig() bool {
	_, ok := _this.Get().(SimpleBooleanConfig_SimpleBooleanConfig)
	return ok
}

func (CompanionStruct_SimpleBooleanConfig_) Default() SimpleBooleanConfig {
	return Companion_SimpleBooleanConfig_.Create_SimpleBooleanConfig_()
}

func (_ CompanionStruct_SimpleBooleanConfig_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_SimpleBooleanConfig_.Create_SimpleBooleanConfig_(), true
		default:
			return SimpleBooleanConfig{}, false
		}
	}
}

func (_this SimpleBooleanConfig) String() string {
	switch _this.Get().(type) {
	case nil:
		return "null"
	case SimpleBooleanConfig_SimpleBooleanConfig:
		{
			return "SimpleTypesBooleanTypes.SimpleBooleanConfig.SimpleBooleanConfig"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this SimpleBooleanConfig) Equals(other SimpleBooleanConfig) bool {
	switch _this.Get().(type) {
	case SimpleBooleanConfig_SimpleBooleanConfig:
		{
			_, ok := other.Get().(SimpleBooleanConfig_SimpleBooleanConfig)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this SimpleBooleanConfig) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(SimpleBooleanConfig)
	return ok && _this.Equals(typed)
}

func Type_SimpleBooleanConfig_() _dafny.TypeDescriptor {
	return type_SimpleBooleanConfig_{}
}

type type_SimpleBooleanConfig_ struct {
}

func (_this type_SimpleBooleanConfig_) Default() interface{} {
	return Companion_SimpleBooleanConfig_.Default()
}

func (_this type_SimpleBooleanConfig_) String() string {
	return "simpletypesbooleaninternaldafnytypes.SimpleBooleanConfig"
}
func (_this SimpleBooleanConfig) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = SimpleBooleanConfig{}

// End of datatype SimpleBooleanConfig

// Definition of class ISimpleTypesBooleanClientCallHistory
type ISimpleTypesBooleanClientCallHistory struct {
	dummy byte
}

func New_ISimpleTypesBooleanClientCallHistory_() *ISimpleTypesBooleanClientCallHistory {
	_this := ISimpleTypesBooleanClientCallHistory{}

	return &_this
}

type CompanionStruct_ISimpleTypesBooleanClientCallHistory_ struct {
}

var Companion_ISimpleTypesBooleanClientCallHistory_ = CompanionStruct_ISimpleTypesBooleanClientCallHistory_{}

func (_this *ISimpleTypesBooleanClientCallHistory) Equals(other *ISimpleTypesBooleanClientCallHistory) bool {
	return _this == other
}

func (_this *ISimpleTypesBooleanClientCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimpleTypesBooleanClientCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimpleTypesBooleanClientCallHistory) String() string {
	return "simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClientCallHistory"
}

func Type_ISimpleTypesBooleanClientCallHistory_() _dafny.TypeDescriptor {
	return type_ISimpleTypesBooleanClientCallHistory_{}
}

type type_ISimpleTypesBooleanClientCallHistory_ struct {
}

func (_this type_ISimpleTypesBooleanClientCallHistory_) Default() interface{} {
	return (*ISimpleTypesBooleanClientCallHistory)(nil)
}

func (_this type_ISimpleTypesBooleanClientCallHistory_) String() string {
	return "simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClientCallHistory"
}
func (_this *ISimpleTypesBooleanClientCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimpleTypesBooleanClientCallHistory{}

// End of class ISimpleTypesBooleanClientCallHistory

// Definition of trait ISimpleTypesBooleanClient
type ISimpleTypesBooleanClient interface {
	String() string
	GetBoolean(input GetBooleanInput) Wrappers.Result
}
type CompanionStruct_ISimpleTypesBooleanClient_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimpleTypesBooleanClient_ = CompanionStruct_ISimpleTypesBooleanClient_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimpleTypesBooleanClient_) CastTo_(x interface{}) ISimpleTypesBooleanClient {
	var t ISimpleTypesBooleanClient
	t, _ = x.(ISimpleTypesBooleanClient)
	return t
}

// End of trait ISimpleTypesBooleanClient

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
	case nil:
		return "null"
	case Error_CollectionOfErrors:
		{
			return "SimpleTypesBooleanTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + _dafny.String(data.Message) + ")"
		}
	case Error_Opaque:
		{
			return "SimpleTypesBooleanTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Error) Equals(other Error) bool {
	switch data1 := _this.Get().(type) {
	case Error_CollectionOfErrors:
		{
			data2, ok := other.Get().(Error_CollectionOfErrors)
			return ok && data1.List.Equals(data2.List) && data1.Message.Equals(data2.Message)
		}
	case Error_Opaque:
		{
			data2, ok := other.Get().(Error_Opaque)
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
	return "simpletypesbooleaninternaldafnytypes.Error"
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
	return "simpletypesbooleaninternaldafnytypes.OpaqueError"
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
	return "simpletypesbooleaninternaldafnytypes.OpaqueError"
}
