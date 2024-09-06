// Package SimpleAggregateTypes
// Dafny module SimpleAggregateTypes compiled into Go

package SimpleAggregateTypes

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
			return "SimpleAggregateTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
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
	return "SimpleAggregateTypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype GetAggregateInput
type GetAggregateInput struct {
	Data_GetAggregateInput_
}

func (_this GetAggregateInput) Get_() Data_GetAggregateInput_ {
	return _this.Data_GetAggregateInput_
}

type Data_GetAggregateInput_ interface {
	isGetAggregateInput()
}

type CompanionStruct_GetAggregateInput_ struct {
}

var Companion_GetAggregateInput_ = CompanionStruct_GetAggregateInput_{}

type GetAggregateInput_GetAggregateInput struct {
	SimpleStringList Wrappers.Option
	StructureList    Wrappers.Option
	SimpleStringMap  Wrappers.Option
	SimpleIntegerMap Wrappers.Option
	NestedStructure  Wrappers.Option
}

func (GetAggregateInput_GetAggregateInput) isGetAggregateInput() {}

func (CompanionStruct_GetAggregateInput_) Create_GetAggregateInput_(SimpleStringList Wrappers.Option, StructureList Wrappers.Option, SimpleStringMap Wrappers.Option, SimpleIntegerMap Wrappers.Option, NestedStructure Wrappers.Option) GetAggregateInput {
	return GetAggregateInput{GetAggregateInput_GetAggregateInput{SimpleStringList, StructureList, SimpleStringMap, SimpleIntegerMap, NestedStructure}}
}

func (_this GetAggregateInput) Is_GetAggregateInput() bool {
	_, ok := _this.Get_().(GetAggregateInput_GetAggregateInput)
	return ok
}

func (CompanionStruct_GetAggregateInput_) Default() GetAggregateInput {
	return Companion_GetAggregateInput_.Create_GetAggregateInput_(Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default())
}

func (_this GetAggregateInput) Dtor_simpleStringList() Wrappers.Option {
	return _this.Get_().(GetAggregateInput_GetAggregateInput).SimpleStringList
}

func (_this GetAggregateInput) Dtor_structureList() Wrappers.Option {
	return _this.Get_().(GetAggregateInput_GetAggregateInput).StructureList
}

func (_this GetAggregateInput) Dtor_simpleStringMap() Wrappers.Option {
	return _this.Get_().(GetAggregateInput_GetAggregateInput).SimpleStringMap
}

func (_this GetAggregateInput) Dtor_simpleIntegerMap() Wrappers.Option {
	return _this.Get_().(GetAggregateInput_GetAggregateInput).SimpleIntegerMap
}

func (_this GetAggregateInput) Dtor_nestedStructure() Wrappers.Option {
	return _this.Get_().(GetAggregateInput_GetAggregateInput).NestedStructure
}

func (_this GetAggregateInput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetAggregateInput_GetAggregateInput:
		{
			return "SimpleAggregateTypes.GetAggregateInput.GetAggregateInput" + "(" + _dafny.String(data.SimpleStringList) + ", " + _dafny.String(data.StructureList) + ", " + _dafny.String(data.SimpleStringMap) + ", " + _dafny.String(data.SimpleIntegerMap) + ", " + _dafny.String(data.NestedStructure) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetAggregateInput) Equals(other GetAggregateInput) bool {
	switch data1 := _this.Get_().(type) {
	case GetAggregateInput_GetAggregateInput:
		{
			data2, ok := other.Get_().(GetAggregateInput_GetAggregateInput)
			return ok && data1.SimpleStringList.Equals(data2.SimpleStringList) && data1.StructureList.Equals(data2.StructureList) && data1.SimpleStringMap.Equals(data2.SimpleStringMap) && data1.SimpleIntegerMap.Equals(data2.SimpleIntegerMap) && data1.NestedStructure.Equals(data2.NestedStructure)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetAggregateInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetAggregateInput)
	return ok && _this.Equals(typed)
}

func Type_GetAggregateInput_() _dafny.TypeDescriptor {
	return type_GetAggregateInput_{}
}

type type_GetAggregateInput_ struct {
}

func (_this type_GetAggregateInput_) Default() interface{} {
	return Companion_GetAggregateInput_.Default()
}

func (_this type_GetAggregateInput_) String() string {
	return "SimpleAggregateTypes.GetAggregateInput"
}
func (_this GetAggregateInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetAggregateInput{}

// End of datatype GetAggregateInput

// Definition of datatype GetAggregateOutput
type GetAggregateOutput struct {
	Data_GetAggregateOutput_
}

func (_this GetAggregateOutput) Get_() Data_GetAggregateOutput_ {
	return _this.Data_GetAggregateOutput_
}

type Data_GetAggregateOutput_ interface {
	isGetAggregateOutput()
}

type CompanionStruct_GetAggregateOutput_ struct {
}

var Companion_GetAggregateOutput_ = CompanionStruct_GetAggregateOutput_{}

type GetAggregateOutput_GetAggregateOutput struct {
	SimpleStringList Wrappers.Option
	StructureList    Wrappers.Option
	SimpleStringMap  Wrappers.Option
	SimpleIntegerMap Wrappers.Option
	NestedStructure  Wrappers.Option
}

func (GetAggregateOutput_GetAggregateOutput) isGetAggregateOutput() {}

func (CompanionStruct_GetAggregateOutput_) Create_GetAggregateOutput_(SimpleStringList Wrappers.Option, StructureList Wrappers.Option, SimpleStringMap Wrappers.Option, SimpleIntegerMap Wrappers.Option, NestedStructure Wrappers.Option) GetAggregateOutput {
	return GetAggregateOutput{GetAggregateOutput_GetAggregateOutput{SimpleStringList, StructureList, SimpleStringMap, SimpleIntegerMap, NestedStructure}}
}

func (_this GetAggregateOutput) Is_GetAggregateOutput() bool {
	_, ok := _this.Get_().(GetAggregateOutput_GetAggregateOutput)
	return ok
}

func (CompanionStruct_GetAggregateOutput_) Default() GetAggregateOutput {
	return Companion_GetAggregateOutput_.Create_GetAggregateOutput_(Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default())
}

func (_this GetAggregateOutput) Dtor_simpleStringList() Wrappers.Option {
	return _this.Get_().(GetAggregateOutput_GetAggregateOutput).SimpleStringList
}

func (_this GetAggregateOutput) Dtor_structureList() Wrappers.Option {
	return _this.Get_().(GetAggregateOutput_GetAggregateOutput).StructureList
}

func (_this GetAggregateOutput) Dtor_simpleStringMap() Wrappers.Option {
	return _this.Get_().(GetAggregateOutput_GetAggregateOutput).SimpleStringMap
}

func (_this GetAggregateOutput) Dtor_simpleIntegerMap() Wrappers.Option {
	return _this.Get_().(GetAggregateOutput_GetAggregateOutput).SimpleIntegerMap
}

func (_this GetAggregateOutput) Dtor_nestedStructure() Wrappers.Option {
	return _this.Get_().(GetAggregateOutput_GetAggregateOutput).NestedStructure
}

func (_this GetAggregateOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case GetAggregateOutput_GetAggregateOutput:
		{
			return "SimpleAggregateTypes.GetAggregateOutput.GetAggregateOutput" + "(" + _dafny.String(data.SimpleStringList) + ", " + _dafny.String(data.StructureList) + ", " + _dafny.String(data.SimpleStringMap) + ", " + _dafny.String(data.SimpleIntegerMap) + ", " + _dafny.String(data.NestedStructure) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this GetAggregateOutput) Equals(other GetAggregateOutput) bool {
	switch data1 := _this.Get_().(type) {
	case GetAggregateOutput_GetAggregateOutput:
		{
			data2, ok := other.Get_().(GetAggregateOutput_GetAggregateOutput)
			return ok && data1.SimpleStringList.Equals(data2.SimpleStringList) && data1.StructureList.Equals(data2.StructureList) && data1.SimpleStringMap.Equals(data2.SimpleStringMap) && data1.SimpleIntegerMap.Equals(data2.SimpleIntegerMap) && data1.NestedStructure.Equals(data2.NestedStructure)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this GetAggregateOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(GetAggregateOutput)
	return ok && _this.Equals(typed)
}

func Type_GetAggregateOutput_() _dafny.TypeDescriptor {
	return type_GetAggregateOutput_{}
}

type type_GetAggregateOutput_ struct {
}

func (_this type_GetAggregateOutput_) Default() interface{} {
	return Companion_GetAggregateOutput_.Default()
}

func (_this type_GetAggregateOutput_) String() string {
	return "SimpleAggregateTypes.GetAggregateOutput"
}
func (_this GetAggregateOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = GetAggregateOutput{}

// End of datatype GetAggregateOutput

// Definition of datatype NestedStructure
type NestedStructure struct {
	Data_NestedStructure_
}

func (_this NestedStructure) Get_() Data_NestedStructure_ {
	return _this.Data_NestedStructure_
}

type Data_NestedStructure_ interface {
	isNestedStructure()
}

type CompanionStruct_NestedStructure_ struct {
}

var Companion_NestedStructure_ = CompanionStruct_NestedStructure_{}

type NestedStructure_NestedStructure struct {
	StringStructure Wrappers.Option
}

func (NestedStructure_NestedStructure) isNestedStructure() {}

func (CompanionStruct_NestedStructure_) Create_NestedStructure_(StringStructure Wrappers.Option) NestedStructure {
	return NestedStructure{NestedStructure_NestedStructure{StringStructure}}
}

func (_this NestedStructure) Is_NestedStructure() bool {
	_, ok := _this.Get_().(NestedStructure_NestedStructure)
	return ok
}

func (CompanionStruct_NestedStructure_) Default() NestedStructure {
	return Companion_NestedStructure_.Create_NestedStructure_(Wrappers.Companion_Option_.Default())
}

func (_this NestedStructure) Dtor_stringStructure() Wrappers.Option {
	return _this.Get_().(NestedStructure_NestedStructure).StringStructure
}

func (_this NestedStructure) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case NestedStructure_NestedStructure:
		{
			return "SimpleAggregateTypes.NestedStructure.NestedStructure" + "(" + _dafny.String(data.StringStructure) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this NestedStructure) Equals(other NestedStructure) bool {
	switch data1 := _this.Get_().(type) {
	case NestedStructure_NestedStructure:
		{
			data2, ok := other.Get_().(NestedStructure_NestedStructure)
			return ok && data1.StringStructure.Equals(data2.StringStructure)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this NestedStructure) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(NestedStructure)
	return ok && _this.Equals(typed)
}

func Type_NestedStructure_() _dafny.TypeDescriptor {
	return type_NestedStructure_{}
}

type type_NestedStructure_ struct {
}

func (_this type_NestedStructure_) Default() interface{} {
	return Companion_NestedStructure_.Default()
}

func (_this type_NestedStructure_) String() string {
	return "SimpleAggregateTypes.NestedStructure"
}
func (_this NestedStructure) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = NestedStructure{}

// End of datatype NestedStructure

// Definition of class ISimpleAggregateClientCallHistory
type ISimpleAggregateClientCallHistory struct {
	dummy byte
}

func New_ISimpleAggregateClientCallHistory_() *ISimpleAggregateClientCallHistory {
	_this := ISimpleAggregateClientCallHistory{}

	return &_this
}

type CompanionStruct_ISimpleAggregateClientCallHistory_ struct {
}

var Companion_ISimpleAggregateClientCallHistory_ = CompanionStruct_ISimpleAggregateClientCallHistory_{}

func (_this *ISimpleAggregateClientCallHistory) Equals(other *ISimpleAggregateClientCallHistory) bool {
	return _this == other
}

func (_this *ISimpleAggregateClientCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimpleAggregateClientCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimpleAggregateClientCallHistory) String() string {
	return "SimpleAggregateTypes.ISimpleAggregateClientCallHistory"
}

func Type_ISimpleAggregateClientCallHistory_() _dafny.TypeDescriptor {
	return type_ISimpleAggregateClientCallHistory_{}
}

type type_ISimpleAggregateClientCallHistory_ struct {
}

func (_this type_ISimpleAggregateClientCallHistory_) Default() interface{} {
	return (*ISimpleAggregateClientCallHistory)(nil)
}

func (_this type_ISimpleAggregateClientCallHistory_) String() string {
	return "SimpleAggregateTypes.ISimpleAggregateClientCallHistory"
}
func (_this *ISimpleAggregateClientCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimpleAggregateClientCallHistory{}

// End of class ISimpleAggregateClientCallHistory

// Definition of trait ISimpleAggregateClient
type ISimpleAggregateClient interface {
	String() string
	GetAggregate(input GetAggregateInput) Wrappers.Result
	GetAggregateKnownValueTest(input GetAggregateInput) Wrappers.Result
}
type CompanionStruct_ISimpleAggregateClient_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimpleAggregateClient_ = CompanionStruct_ISimpleAggregateClient_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimpleAggregateClient_) CastTo_(x interface{}) ISimpleAggregateClient {
	var t ISimpleAggregateClient
	t, _ = x.(ISimpleAggregateClient)
	return t
}

// End of trait ISimpleAggregateClient

// Definition of datatype SimpleAggregateConfig
type SimpleAggregateConfig struct {
	Data_SimpleAggregateConfig_
}

func (_this SimpleAggregateConfig) Get_() Data_SimpleAggregateConfig_ {
	return _this.Data_SimpleAggregateConfig_
}

type Data_SimpleAggregateConfig_ interface {
	isSimpleAggregateConfig()
}

type CompanionStruct_SimpleAggregateConfig_ struct {
}

var Companion_SimpleAggregateConfig_ = CompanionStruct_SimpleAggregateConfig_{}

type SimpleAggregateConfig_SimpleAggregateConfig struct {
}

func (SimpleAggregateConfig_SimpleAggregateConfig) isSimpleAggregateConfig() {}

func (CompanionStruct_SimpleAggregateConfig_) Create_SimpleAggregateConfig_() SimpleAggregateConfig {
	return SimpleAggregateConfig{SimpleAggregateConfig_SimpleAggregateConfig{}}
}

func (_this SimpleAggregateConfig) Is_SimpleAggregateConfig() bool {
	_, ok := _this.Get_().(SimpleAggregateConfig_SimpleAggregateConfig)
	return ok
}

func (CompanionStruct_SimpleAggregateConfig_) Default() SimpleAggregateConfig {
	return Companion_SimpleAggregateConfig_.Create_SimpleAggregateConfig_()
}

func (_ CompanionStruct_SimpleAggregateConfig_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_SimpleAggregateConfig_.Create_SimpleAggregateConfig_(), true
		default:
			return SimpleAggregateConfig{}, false
		}
	}
}

func (_this SimpleAggregateConfig) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case SimpleAggregateConfig_SimpleAggregateConfig:
		{
			return "SimpleAggregateTypes.SimpleAggregateConfig.SimpleAggregateConfig"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this SimpleAggregateConfig) Equals(other SimpleAggregateConfig) bool {
	switch _this.Get_().(type) {
	case SimpleAggregateConfig_SimpleAggregateConfig:
		{
			_, ok := other.Get_().(SimpleAggregateConfig_SimpleAggregateConfig)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this SimpleAggregateConfig) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(SimpleAggregateConfig)
	return ok && _this.Equals(typed)
}

func Type_SimpleAggregateConfig_() _dafny.TypeDescriptor {
	return type_SimpleAggregateConfig_{}
}

type type_SimpleAggregateConfig_ struct {
}

func (_this type_SimpleAggregateConfig_) Default() interface{} {
	return Companion_SimpleAggregateConfig_.Default()
}

func (_this type_SimpleAggregateConfig_) String() string {
	return "SimpleAggregateTypes.SimpleAggregateConfig"
}
func (_this SimpleAggregateConfig) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = SimpleAggregateConfig{}

// End of datatype SimpleAggregateConfig

// Definition of datatype StringStructure
type StringStructure struct {
	Data_StringStructure_
}

func (_this StringStructure) Get_() Data_StringStructure_ {
	return _this.Data_StringStructure_
}

type Data_StringStructure_ interface {
	isStringStructure()
}

type CompanionStruct_StringStructure_ struct {
}

var Companion_StringStructure_ = CompanionStruct_StringStructure_{}

type StringStructure_StringStructure struct {
	Value Wrappers.Option
}

func (StringStructure_StringStructure) isStringStructure() {}

func (CompanionStruct_StringStructure_) Create_StringStructure_(Value Wrappers.Option) StringStructure {
	return StringStructure{StringStructure_StringStructure{Value}}
}

func (_this StringStructure) Is_StringStructure() bool {
	_, ok := _this.Get_().(StringStructure_StringStructure)
	return ok
}

func (CompanionStruct_StringStructure_) Default() StringStructure {
	return Companion_StringStructure_.Create_StringStructure_(Wrappers.Companion_Option_.Default())
}

func (_this StringStructure) Dtor_value() Wrappers.Option {
	return _this.Get_().(StringStructure_StringStructure).Value
}

func (_this StringStructure) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case StringStructure_StringStructure:
		{
			return "SimpleAggregateTypes.StringStructure.StringStructure" + "(" + _dafny.String(data.Value) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this StringStructure) Equals(other StringStructure) bool {
	switch data1 := _this.Get_().(type) {
	case StringStructure_StringStructure:
		{
			data2, ok := other.Get_().(StringStructure_StringStructure)
			return ok && data1.Value.Equals(data2.Value)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this StringStructure) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(StringStructure)
	return ok && _this.Equals(typed)
}

func Type_StringStructure_() _dafny.TypeDescriptor {
	return type_StringStructure_{}
}

type type_StringStructure_ struct {
}

func (_this type_StringStructure_) Default() interface{} {
	return Companion_StringStructure_.Default()
}

func (_this type_StringStructure_) String() string {
	return "SimpleAggregateTypes.StringStructure"
}
func (_this StringStructure) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = StringStructure{}

// End of datatype StringStructure

// Definition of datatype StructureListElement
type StructureListElement struct {
	Data_StructureListElement_
}

func (_this StructureListElement) Get_() Data_StructureListElement_ {
	return _this.Data_StructureListElement_
}

type Data_StructureListElement_ interface {
	isStructureListElement()
}

type CompanionStruct_StructureListElement_ struct {
}

var Companion_StructureListElement_ = CompanionStruct_StructureListElement_{}

type StructureListElement_StructureListElement struct {
	StringValue  Wrappers.Option
	IntegerValue Wrappers.Option
}

func (StructureListElement_StructureListElement) isStructureListElement() {}

func (CompanionStruct_StructureListElement_) Create_StructureListElement_(StringValue Wrappers.Option, IntegerValue Wrappers.Option) StructureListElement {
	return StructureListElement{StructureListElement_StructureListElement{StringValue, IntegerValue}}
}

func (_this StructureListElement) Is_StructureListElement() bool {
	_, ok := _this.Get_().(StructureListElement_StructureListElement)
	return ok
}

func (CompanionStruct_StructureListElement_) Default() StructureListElement {
	return Companion_StructureListElement_.Create_StructureListElement_(Wrappers.Companion_Option_.Default(), Wrappers.Companion_Option_.Default())
}

func (_this StructureListElement) Dtor_stringValue() Wrappers.Option {
	return _this.Get_().(StructureListElement_StructureListElement).StringValue
}

func (_this StructureListElement) Dtor_integerValue() Wrappers.Option {
	return _this.Get_().(StructureListElement_StructureListElement).IntegerValue
}

func (_this StructureListElement) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case StructureListElement_StructureListElement:
		{
			return "SimpleAggregateTypes.StructureListElement.StructureListElement" + "(" + _dafny.String(data.StringValue) + ", " + _dafny.String(data.IntegerValue) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this StructureListElement) Equals(other StructureListElement) bool {
	switch data1 := _this.Get_().(type) {
	case StructureListElement_StructureListElement:
		{
			data2, ok := other.Get_().(StructureListElement_StructureListElement)
			return ok && data1.StringValue.Equals(data2.StringValue) && data1.IntegerValue.Equals(data2.IntegerValue)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this StructureListElement) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(StructureListElement)
	return ok && _this.Equals(typed)
}

func Type_StructureListElement_() _dafny.TypeDescriptor {
	return type_StructureListElement_{}
}

type type_StructureListElement_ struct {
}

func (_this type_StructureListElement_) Default() interface{} {
	return Companion_StructureListElement_.Default()
}

func (_this type_StructureListElement_) String() string {
	return "SimpleAggregateTypes.StructureListElement"
}
func (_this StructureListElement) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = StructureListElement{}

// End of datatype StructureListElement

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
	return Companion_Error_.Create_CollectionOfErrors_(_dafny.EmptySeq, _dafny.EmptySeq.SetString())
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
			return "SimpleAggregateTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + _dafny.String(data.Message) + ")"
		}
	case Error_Opaque:
		{
			return "SimpleAggregateTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
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
	return "SimpleAggregateTypes.Error"
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
	return "SimpleAggregateTypes.OpaqueError"
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
	return "SimpleAggregateTypes.OpaqueError"
}
func (_this *CompanionStruct_OpaqueError_) Is_(__source Error) bool {
	var _0_e Error = (__source)
	_ = _0_e
	return (_0_e).Is_Opaque()
}
