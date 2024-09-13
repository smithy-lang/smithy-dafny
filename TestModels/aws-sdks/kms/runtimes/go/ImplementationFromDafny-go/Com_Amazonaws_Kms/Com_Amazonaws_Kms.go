// Package Com_Amazonaws_Kms
// Dafny module Com_Amazonaws_Kms compiled into Go

package Com_Amazonaws_Kms

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kms/ComAmazonawsKmsTypes"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ ComAmazonawsKmsTypes.Dummy__

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

var Companion_Default___ = CompanionStruct_Default___{}

func (_this *Default__) Equals(other *Default__) bool {
	return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*Default__)
	return ok && _this.Equals(other)
}

func (*Default__) String() string {
	return "Com_Amazonaws_Kms.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultKMSClientConfigType() KMSClientConfigType {
	return Companion_KMSClientConfigType_.Create_KMSClientConfigType_()
}
func (_static *CompanionStruct_Default___) CreateSuccessOfClient(client ComAmazonawsKmsTypes.IKMSClient) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(client)
}
func (_static *CompanionStruct_Default___) CreateFailureOfError(error_ ComAmazonawsKmsTypes.Error) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}

// End of class Default__

// Definition of datatype KMSClientConfigType
type KMSClientConfigType struct {
	Data_KMSClientConfigType_
}

func (_this KMSClientConfigType) Get_() Data_KMSClientConfigType_ {
	return _this.Data_KMSClientConfigType_
}

type Data_KMSClientConfigType_ interface {
	isKMSClientConfigType()
}

type CompanionStruct_KMSClientConfigType_ struct {
}

var Companion_KMSClientConfigType_ = CompanionStruct_KMSClientConfigType_{}

type KMSClientConfigType_KMSClientConfigType struct {
}

func (KMSClientConfigType_KMSClientConfigType) isKMSClientConfigType() {}

func (CompanionStruct_KMSClientConfigType_) Create_KMSClientConfigType_() KMSClientConfigType {
	return KMSClientConfigType{KMSClientConfigType_KMSClientConfigType{}}
}

func (_this KMSClientConfigType) Is_KMSClientConfigType() bool {
	_, ok := _this.Get_().(KMSClientConfigType_KMSClientConfigType)
	return ok
}

func (CompanionStruct_KMSClientConfigType_) Default() KMSClientConfigType {
	return Companion_KMSClientConfigType_.Create_KMSClientConfigType_()
}

func (_ CompanionStruct_KMSClientConfigType_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_KMSClientConfigType_.Create_KMSClientConfigType_(), true
		default:
			return KMSClientConfigType{}, false
		}
	}
}

func (_this KMSClientConfigType) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case KMSClientConfigType_KMSClientConfigType:
		{
			return "Kms.KMSClientConfigType.KMSClientConfigType"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this KMSClientConfigType) Equals(other KMSClientConfigType) bool {
	switch _this.Get_().(type) {
	case KMSClientConfigType_KMSClientConfigType:
		{
			_, ok := other.Get_().(KMSClientConfigType_KMSClientConfigType)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this KMSClientConfigType) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(KMSClientConfigType)
	return ok && _this.Equals(typed)
}

func Type_KMSClientConfigType_() _dafny.TypeDescriptor {
	return type_KMSClientConfigType_{}
}

type type_KMSClientConfigType_ struct {
}

func (_this type_KMSClientConfigType_) Default() interface{} {
	return Companion_KMSClientConfigType_.Default()
}

func (_this type_KMSClientConfigType_) String() string {
	return "Com_Amazonaws_Kms.KMSClientConfigType"
}
func (_this KMSClientConfigType) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = KMSClientConfigType{}

// End of datatype KMSClientConfigType
