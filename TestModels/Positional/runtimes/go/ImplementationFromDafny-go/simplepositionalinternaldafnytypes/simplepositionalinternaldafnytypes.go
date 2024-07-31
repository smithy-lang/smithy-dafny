// Package simplepositionalinternaldafnytypes
// Dafny module simplepositionalinternaldafnytypes compiled into Go

package simplepositionalinternaldafnytypes

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__

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
			return "SimplePositionalTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
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
	return "simplepositionalinternaldafnytypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype GetNameInput
type GetNameInput struct {
	Data_GetNameInput_
}

func (_this GetNameInput) Get_() Data_GetNameInput_ {
	return _this.Data_GetNameInput_
}

type Data_GetNameInput_ interface {
	isGetNameInput()
}

type CompanionStruct_GetNameInput_ struct {
}

var Companion_GetNameInput_ = CompanionStruct_GetNameInput_{}

type GetNameInput_GetNameInput struct {
}

func (GetNameInput_GetNameInput) isGetNameInput() {}

func (CompanionStruct_GetNameInput_) Create_GetNameInput_() GetNameInput {
	return GetNameInput{GetNameInput_GetNameInput{}}
}

func (_this GetNameInput) Is_GetNameInput() bool {
	_, ok := _this.Get_().(GetNameInput_GetNameInput)
	return ok
}

func (CompanionStruct_GetNameInput_) Default() GetNameInput {
	return Companion_GetNameInput_.Create_GetNameInput_()
}

func (_ CompanionStruct_GetNameInput_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_GetNameInput_.Create_GetNameInput_(), true
		default:
			return GetNameInput{}, false
		}
	}
}

func (_this GetNameInput) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case GetNameInput_GetNameInput:
		{
			return "SimplePositionalTypes.GetNameInput.GetNameInput"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetNameInput) Equals(other GetNameInput) bool {
	switch _this.Get_().(type) {
	case GetNameInput_GetNameInput:
		{
			_, ok := other.Get_().(GetNameInput_GetNameInput)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetNameInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetNameInput)
	return ok && _this.Equals(typed)
}

func Type_GetNameInput_() _dafny.TypeDescriptor {
	return type_GetNameInput_{}
}

type type_GetNameInput_ struct {
}

func (_this type_GetNameInput_) Default() interface{} {
	return Companion_GetNameInput_.Default()
}

func (_this type_GetNameInput_) String() string {
	return "simplepositionalinternaldafnytypes.GetNameInput"
}
func (_this GetNameInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetNameInput{}

// End of datatype GetNameInput

// Definition of datatype GetNameOutput
type GetNameOutput struct {
	Data_GetNameOutput_
}

func (_this GetNameOutput) Get_() Data_GetNameOutput_ {
	return _this.Data_GetNameOutput_
}

type Data_GetNameOutput_ interface {
	isGetNameOutput()
}

type CompanionStruct_GetNameOutput_ struct {
}

var Companion_GetNameOutput_ = CompanionStruct_GetNameOutput_{}

type GetNameOutput_GetNameOutput struct {
	Name _dafny.Sequence
}

func (GetNameOutput_GetNameOutput) isGetNameOutput() {}

func (CompanionStruct_GetNameOutput_) Create_GetNameOutput_(Name _dafny.Sequence) GetNameOutput {
	return GetNameOutput{GetNameOutput_GetNameOutput{Name}}
}

func (_this GetNameOutput) Is_GetNameOutput() bool {
	_, ok := _this.Get_().(GetNameOutput_GetNameOutput)
	return ok
}

func (CompanionStruct_GetNameOutput_) Default() GetNameOutput {
	return Companion_GetNameOutput_.Create_GetNameOutput_(_dafny.EmptySeq.SetString())
}

func (_this GetNameOutput) Dtor_name() _dafny.Sequence {
	return _this.Get_().(GetNameOutput_GetNameOutput).Name
}

func (_this GetNameOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetNameOutput_GetNameOutput:
		{
			return "SimplePositionalTypes.GetNameOutput.GetNameOutput" + "(" + _dafny.String(data.Name) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetNameOutput) Equals(other GetNameOutput) bool {
	switch data1 := _this.Get_().(type) {
	case GetNameOutput_GetNameOutput:
		{
			data2, ok := other.Get_().(GetNameOutput_GetNameOutput)
			return ok && data1.Name.Equals(data2.Name)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetNameOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetNameOutput)
	return ok && _this.Equals(typed)
}

func Type_GetNameOutput_() _dafny.TypeDescriptor {
	return type_GetNameOutput_{}
}

type type_GetNameOutput_ struct {
}

func (_this type_GetNameOutput_) Default() interface{} {
	return Companion_GetNameOutput_.Default()
}

func (_this type_GetNameOutput_) String() string {
	return "simplepositionalinternaldafnytypes.GetNameOutput"
}
func (_this GetNameOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetNameOutput{}

// End of datatype GetNameOutput

// Definition of datatype GetResourceInput
type GetResourceInput struct {
	Data_GetResourceInput_
}

func (_this GetResourceInput) Get_() Data_GetResourceInput_ {
	return _this.Data_GetResourceInput_
}

type Data_GetResourceInput_ interface {
	isGetResourceInput()
}

type CompanionStruct_GetResourceInput_ struct {
}

var Companion_GetResourceInput_ = CompanionStruct_GetResourceInput_{}

type GetResourceInput_GetResourceInput struct {
	Name _dafny.Sequence
}

func (GetResourceInput_GetResourceInput) isGetResourceInput() {}

func (CompanionStruct_GetResourceInput_) Create_GetResourceInput_(Name _dafny.Sequence) GetResourceInput {
	return GetResourceInput{GetResourceInput_GetResourceInput{Name}}
}

func (_this GetResourceInput) Is_GetResourceInput() bool {
	_, ok := _this.Get_().(GetResourceInput_GetResourceInput)
	return ok
}

func (CompanionStruct_GetResourceInput_) Default() GetResourceInput {
	return Companion_GetResourceInput_.Create_GetResourceInput_(_dafny.EmptySeq.SetString())
}

func (_this GetResourceInput) Dtor_name() _dafny.Sequence {
	return _this.Get_().(GetResourceInput_GetResourceInput).Name
}

func (_this GetResourceInput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetResourceInput_GetResourceInput:
		{
			return "SimplePositionalTypes.GetResourceInput.GetResourceInput" + "(" + _dafny.String(data.Name) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetResourceInput) Equals(other GetResourceInput) bool {
	switch data1 := _this.Get_().(type) {
	case GetResourceInput_GetResourceInput:
		{
			data2, ok := other.Get_().(GetResourceInput_GetResourceInput)
			return ok && data1.Name.Equals(data2.Name)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetResourceInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetResourceInput)
	return ok && _this.Equals(typed)
}

func Type_GetResourceInput_() _dafny.TypeDescriptor {
	return type_GetResourceInput_{}
}

type type_GetResourceInput_ struct {
}

func (_this type_GetResourceInput_) Default() interface{} {
	return Companion_GetResourceInput_.Default()
}

func (_this type_GetResourceInput_) String() string {
	return "simplepositionalinternaldafnytypes.GetResourceInput"
}
func (_this GetResourceInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetResourceInput{}

// End of datatype GetResourceInput

// Definition of datatype GetResourceOutput
type GetResourceOutput struct {
	Data_GetResourceOutput_
}

func (_this GetResourceOutput) Get_() Data_GetResourceOutput_ {
	return _this.Data_GetResourceOutput_
}

type Data_GetResourceOutput_ interface {
	isGetResourceOutput()
}

type CompanionStruct_GetResourceOutput_ struct {
}

var Companion_GetResourceOutput_ = CompanionStruct_GetResourceOutput_{}

type GetResourceOutput_GetResourceOutput struct {
	Output ISimpleResource
}

func (GetResourceOutput_GetResourceOutput) isGetResourceOutput() {}

func (CompanionStruct_GetResourceOutput_) Create_GetResourceOutput_(Output ISimpleResource) GetResourceOutput {
	return GetResourceOutput{GetResourceOutput_GetResourceOutput{Output}}
}

func (_this GetResourceOutput) Is_GetResourceOutput() bool {
	_, ok := _this.Get_().(GetResourceOutput_GetResourceOutput)
	return ok
}

func (CompanionStruct_GetResourceOutput_) Default() GetResourceOutput {
	return Companion_GetResourceOutput_.Create_GetResourceOutput_((ISimpleResource)(nil))
}

func (_this GetResourceOutput) Dtor_output() ISimpleResource {
	return _this.Get_().(GetResourceOutput_GetResourceOutput).Output
}

func (_this GetResourceOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetResourceOutput_GetResourceOutput:
		{
			return "SimplePositionalTypes.GetResourceOutput.GetResourceOutput" + "(" + _dafny.String(data.Output) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetResourceOutput) Equals(other GetResourceOutput) bool {
	switch data1 := _this.Get_().(type) {
	case GetResourceOutput_GetResourceOutput:
		{
			data2, ok := other.Get_().(GetResourceOutput_GetResourceOutput)
			return ok && _dafny.AreEqual(data1.Output, data2.Output)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetResourceOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetResourceOutput)
	return ok && _this.Equals(typed)
}

func Type_GetResourceOutput_() _dafny.TypeDescriptor {
	return type_GetResourceOutput_{}
}

type type_GetResourceOutput_ struct {
}

func (_this type_GetResourceOutput_) Default() interface{} {
	return Companion_GetResourceOutput_.Default()
}

func (_this type_GetResourceOutput_) String() string {
	return "simplepositionalinternaldafnytypes.GetResourceOutput"
}
func (_this GetResourceOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetResourceOutput{}

// End of datatype GetResourceOutput

// Definition of class ISimplePositionalClientCallHistory
type ISimplePositionalClientCallHistory struct {
	dummy byte
}

func New_ISimplePositionalClientCallHistory_() *ISimplePositionalClientCallHistory {
	_this := ISimplePositionalClientCallHistory{}

	return &_this
}

type CompanionStruct_ISimplePositionalClientCallHistory_ struct {
}

var Companion_ISimplePositionalClientCallHistory_ = CompanionStruct_ISimplePositionalClientCallHistory_{}

func (_this *ISimplePositionalClientCallHistory) Equals(other *ISimplePositionalClientCallHistory) bool {
	return _this == other
}

func (_this *ISimplePositionalClientCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimplePositionalClientCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimplePositionalClientCallHistory) String() string {
	return "simplepositionalinternaldafnytypes.ISimplePositionalClientCallHistory"
}

func Type_ISimplePositionalClientCallHistory_() _dafny.TypeDescriptor {
	return type_ISimplePositionalClientCallHistory_{}
}

type type_ISimplePositionalClientCallHistory_ struct {
}

func (_this type_ISimplePositionalClientCallHistory_) Default() interface{} {
	return (*ISimplePositionalClientCallHistory)(nil)
}

func (_this type_ISimplePositionalClientCallHistory_) String() string {
	return "simplepositionalinternaldafnytypes.ISimplePositionalClientCallHistory"
}
func (_this *ISimplePositionalClientCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimplePositionalClientCallHistory{}

// End of class ISimplePositionalClientCallHistory

// Definition of trait ISimplePositionalClient
type ISimplePositionalClient interface {
	String() string
	GetResource(input GetResourceInput) Wrappers.Result
	GetResourcePositional(input _dafny.Sequence) Wrappers.Result
}
type CompanionStruct_ISimplePositionalClient_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimplePositionalClient_ = CompanionStruct_ISimplePositionalClient_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimplePositionalClient_) CastTo_(x interface{}) ISimplePositionalClient {
	var t ISimplePositionalClient
	t, _ = x.(ISimplePositionalClient)
	return t
}

// End of trait ISimplePositionalClient

// Definition of datatype SimplePositionalConfig
type SimplePositionalConfig struct {
	Data_SimplePositionalConfig_
}

func (_this SimplePositionalConfig) Get_() Data_SimplePositionalConfig_ {
	return _this.Data_SimplePositionalConfig_
}

type Data_SimplePositionalConfig_ interface {
	isSimplePositionalConfig()
}

type CompanionStruct_SimplePositionalConfig_ struct {
}

var Companion_SimplePositionalConfig_ = CompanionStruct_SimplePositionalConfig_{}

type SimplePositionalConfig_SimplePositionalConfig struct {
}

func (SimplePositionalConfig_SimplePositionalConfig) isSimplePositionalConfig() {}

func (CompanionStruct_SimplePositionalConfig_) Create_SimplePositionalConfig_() SimplePositionalConfig {
	return SimplePositionalConfig{SimplePositionalConfig_SimplePositionalConfig{}}
}

func (_this SimplePositionalConfig) Is_SimplePositionalConfig() bool {
	_, ok := _this.Get_().(SimplePositionalConfig_SimplePositionalConfig)
	return ok
}

func (CompanionStruct_SimplePositionalConfig_) Default() SimplePositionalConfig {
	return Companion_SimplePositionalConfig_.Create_SimplePositionalConfig_()
}

func (_ CompanionStruct_SimplePositionalConfig_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_SimplePositionalConfig_.Create_SimplePositionalConfig_(), true
		default:
			return SimplePositionalConfig{}, false
		}
	}
}

func (_this SimplePositionalConfig) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case SimplePositionalConfig_SimplePositionalConfig:
		{
			return "SimplePositionalTypes.SimplePositionalConfig.SimplePositionalConfig"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this SimplePositionalConfig) Equals(other SimplePositionalConfig) bool {
	switch _this.Get_().(type) {
	case SimplePositionalConfig_SimplePositionalConfig:
		{
			_, ok := other.Get_().(SimplePositionalConfig_SimplePositionalConfig)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this SimplePositionalConfig) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(SimplePositionalConfig)
	return ok && _this.Equals(typed)
}

func Type_SimplePositionalConfig_() _dafny.TypeDescriptor {
	return type_SimplePositionalConfig_{}
}

type type_SimplePositionalConfig_ struct {
}

func (_this type_SimplePositionalConfig_) Default() interface{} {
	return Companion_SimplePositionalConfig_.Default()
}

func (_this type_SimplePositionalConfig_) String() string {
	return "simplepositionalinternaldafnytypes.SimplePositionalConfig"
}
func (_this SimplePositionalConfig) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = SimplePositionalConfig{}

// End of datatype SimplePositionalConfig

// Definition of class ISimpleResourceCallHistory
type ISimpleResourceCallHistory struct {
	dummy byte
}

func New_ISimpleResourceCallHistory_() *ISimpleResourceCallHistory {
	_this := ISimpleResourceCallHistory{}

	return &_this
}

type CompanionStruct_ISimpleResourceCallHistory_ struct {
}

var Companion_ISimpleResourceCallHistory_ = CompanionStruct_ISimpleResourceCallHistory_{}

func (_this *ISimpleResourceCallHistory) Equals(other *ISimpleResourceCallHistory) bool {
	return _this == other
}

func (_this *ISimpleResourceCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimpleResourceCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimpleResourceCallHistory) String() string {
	return "simplepositionalinternaldafnytypes.ISimpleResourceCallHistory"
}

func Type_ISimpleResourceCallHistory_() _dafny.TypeDescriptor {
	return type_ISimpleResourceCallHistory_{}
}

type type_ISimpleResourceCallHistory_ struct {
}

func (_this type_ISimpleResourceCallHistory_) Default() interface{} {
	return (*ISimpleResourceCallHistory)(nil)
}

func (_this type_ISimpleResourceCallHistory_) String() string {
	return "simplepositionalinternaldafnytypes.ISimpleResourceCallHistory"
}
func (_this *ISimpleResourceCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimpleResourceCallHistory{}

// End of class ISimpleResourceCallHistory

// Definition of trait ISimpleResource
type ISimpleResource interface {
	String() string
	GetName(input GetNameInput) Wrappers.Result
	GetName_k(input GetNameInput) Wrappers.Result
}

func (_static *CompanionStruct_ISimpleResource_) GetName(_this ISimpleResource, input GetNameInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(Companion_GetNameOutput_.Default())
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = (_this).GetName_k(input)
		output = _out0
		return output
	}
}

type CompanionStruct_ISimpleResource_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimpleResource_ = CompanionStruct_ISimpleResource_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimpleResource_) CastTo_(x interface{}) ISimpleResource {
	var t ISimpleResource
	t, _ = x.(ISimpleResource)
	return t
}

// End of trait ISimpleResource

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

type Error_SimplePositionalException struct {
	Message _dafny.Sequence
}

func (Error_SimplePositionalException) isError() {}

func (CompanionStruct_Error_) Create_SimplePositionalException_(Message _dafny.Sequence) Error {
	return Error{Error_SimplePositionalException{Message}}
}

func (_this Error) Is_SimplePositionalException() bool {
	_, ok := _this.Get_().(Error_SimplePositionalException)
	return ok
}

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
	return Companion_Error_.Create_SimplePositionalException_(_dafny.EmptySeq.SetString())
}

func (_this Error) Dtor_message() _dafny.Sequence {
	switch data := _this.Get_().(type) {
	case Error_SimplePositionalException:
		return data.Message
	default:
		return data.(Error_CollectionOfErrors).Message
	}
}

func (_this Error) Dtor_list() _dafny.Sequence {
	return _this.Get_().(Error_CollectionOfErrors).List
}

func (_this Error) Dtor_obj() interface{} {
	return _this.Get_().(Error_Opaque).Obj
}

func (_this Error) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case Error_SimplePositionalException:
		{
			return "SimplePositionalTypes.Error.SimplePositionalException" + "(" + _dafny.String(data.Message) + ")"
		}
	case Error_CollectionOfErrors:
		{
			return "SimplePositionalTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + _dafny.String(data.Message) + ")"
		}
	case Error_Opaque:
		{
			return "SimplePositionalTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Error) Equals(other Error) bool {
	switch data1 := _this.Get_().(type) {
	case Error_SimplePositionalException:
		{
			data2, ok := other.Get_().(Error_SimplePositionalException)
			return ok && data1.Message.Equals(data2.Message)
		}
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
	return "simplepositionalinternaldafnytypes.Error"
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
	return "simplepositionalinternaldafnytypes.OpaqueError"
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
	return "simplepositionalinternaldafnytypes.OpaqueError"
}
func (_this *CompanionStruct_OpaqueError_) Is_(__source Error) bool {
	var _0_e Error = (__source)
	_ = _0_e
	return (_0_e).Is_Opaque()
}
