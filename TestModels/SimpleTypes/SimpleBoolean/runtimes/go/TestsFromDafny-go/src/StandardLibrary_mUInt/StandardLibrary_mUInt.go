// Package StandardLibrary_mUInt
// Dafny module StandardLibrary_mUInt compiled into Go

package StandardLibrary_mUInt

import (
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
)

var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__

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
	return "StandardLibrary_mUInt.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) UInt8Less(a uint8, b uint8) bool {
	return (a) < (b)
}
func (_static *CompanionStruct_Default___) HasUint16Len(s _dafny.Sequence) bool {
	return (_dafny.IntOfUint32((s).Cardinality())).Cmp(Companion_Default___.UINT16__LIMIT()) < 0
}
func (_static *CompanionStruct_Default___) HasUint32Len(s _dafny.Sequence) bool {
	return (_dafny.IntOfUint32((s).Cardinality())).Cmp(Companion_Default___.UINT32__LIMIT()) < 0
}
func (_static *CompanionStruct_Default___) HasUint64Len(s _dafny.Sequence) bool {
	return (_dafny.IntOfUint32((s).Cardinality())).Cmp(Companion_Default___.UINT64__LIMIT()) < 0
}
func (_static *CompanionStruct_Default___) UInt16ToSeq(x uint16) _dafny.Sequence {
	var _16_b0 uint8 = uint8((x) / (uint16(256)))
	_ = _16_b0
	var _17_b1 uint8 = uint8((x) % (uint16(256)))
	_ = _17_b1
	return _dafny.SeqOf(_16_b0, _17_b1)
}
func (_static *CompanionStruct_Default___) SeqToUInt16(s _dafny.Sequence) uint16 {
	var _18_x0 uint16 = (uint16((s).Select(0).(uint8))) * (uint16(256))
	_ = _18_x0
	return (_18_x0) + (uint16((s).Select(1).(uint8)))
}
func (_static *CompanionStruct_Default___) UInt32ToSeq(x uint32) _dafny.Sequence {
	var _19_b0 uint8 = uint8((x) / (uint32(16777216)))
	_ = _19_b0
	var _20_x0 uint32 = (x) - (func() uint32 { return ((uint32(_19_b0)) * (uint32(16777216))) })()
	_ = _20_x0
	var _21_b1 uint8 = uint8((_20_x0) / (uint32(65536)))
	_ = _21_b1
	var _22_x1 uint32 = (_20_x0) - (func() uint32 { return ((uint32(_21_b1)) * (uint32(65536))) })()
	_ = _22_x1
	var _23_b2 uint8 = uint8((_22_x1) / (uint32(256)))
	_ = _23_b2
	var _24_b3 uint8 = uint8((_22_x1) % (uint32(256)))
	_ = _24_b3
	return _dafny.SeqOf(_19_b0, _21_b1, _23_b2, _24_b3)
}
func (_static *CompanionStruct_Default___) SeqToUInt32(s _dafny.Sequence) uint32 {
	var _25_x0 uint32 = (uint32((s).Select(0).(uint8))) * (uint32(16777216))
	_ = _25_x0
	var _26_x1 uint32 = (_25_x0) + ((uint32((s).Select(1).(uint8))) * (uint32(65536)))
	_ = _26_x1
	var _27_x2 uint32 = (_26_x1) + ((uint32((s).Select(2).(uint8))) * (uint32(256)))
	_ = _27_x2
	return (_27_x2) + (uint32((s).Select(3).(uint8)))
}
func (_static *CompanionStruct_Default___) UInt64ToSeq(x uint64) _dafny.Sequence {
	var _28_b0 uint8 = uint8((x) / (uint64(72057594037927936)))
	_ = _28_b0
	var _29_x0 uint64 = (x) - (func() uint64 { return ((uint64(_28_b0)) * (uint64(72057594037927936))) })()
	_ = _29_x0
	var _30_b1 uint8 = uint8((_29_x0) / (uint64(281474976710656)))
	_ = _30_b1
	var _31_x1 uint64 = (_29_x0) - (func() uint64 { return ((uint64(_30_b1)) * (uint64(281474976710656))) })()
	_ = _31_x1
	var _32_b2 uint8 = uint8((_31_x1) / (uint64(1099511627776)))
	_ = _32_b2
	var _33_x2 uint64 = (_31_x1) - (func() uint64 { return ((uint64(_32_b2)) * (uint64(1099511627776))) })()
	_ = _33_x2
	var _34_b3 uint8 = uint8((_33_x2) / (uint64(4294967296)))
	_ = _34_b3
	var _35_x3 uint64 = (_33_x2) - (func() uint64 { return ((uint64(_34_b3)) * (uint64(4294967296))) })()
	_ = _35_x3
	var _36_b4 uint8 = uint8((_35_x3) / (uint64(16777216)))
	_ = _36_b4
	var _37_x4 uint64 = (_35_x3) - (func() uint64 { return ((uint64(_36_b4)) * (uint64(16777216))) })()
	_ = _37_x4
	var _38_b5 uint8 = uint8((_37_x4) / (uint64(65536)))
	_ = _38_b5
	var _39_x5 uint64 = (_37_x4) - (func() uint64 { return ((uint64(_38_b5)) * (uint64(65536))) })()
	_ = _39_x5
	var _40_b6 uint8 = uint8((_39_x5) / (uint64(256)))
	_ = _40_b6
	var _41_b7 uint8 = uint8((_39_x5) % (uint64(256)))
	_ = _41_b7
	return _dafny.SeqOf(_28_b0, _30_b1, _32_b2, _34_b3, _36_b4, _38_b5, _40_b6, _41_b7)
}
func (_static *CompanionStruct_Default___) SeqToUInt64(s _dafny.Sequence) uint64 {
	var _42_x0 uint64 = (uint64((s).Select(0).(uint8))) * (uint64(72057594037927936))
	_ = _42_x0
	var _43_x1 uint64 = (_42_x0) + ((uint64((s).Select(1).(uint8))) * (uint64(281474976710656)))
	_ = _43_x1
	var _44_x2 uint64 = (_43_x1) + ((uint64((s).Select(2).(uint8))) * (uint64(1099511627776)))
	_ = _44_x2
	var _45_x3 uint64 = (_44_x2) + ((uint64((s).Select(3).(uint8))) * (uint64(4294967296)))
	_ = _45_x3
	var _46_x4 uint64 = (_45_x3) + ((uint64((s).Select(4).(uint8))) * (uint64(16777216)))
	_ = _46_x4
	var _47_x5 uint64 = (_46_x4) + ((uint64((s).Select(5).(uint8))) * (uint64(65536)))
	_ = _47_x5
	var _48_x6 uint64 = (_47_x5) + ((uint64((s).Select(6).(uint8))) * (uint64(256)))
	_ = _48_x6
	var _49_x uint64 = (_48_x6) + (uint64((s).Select(7).(uint8)))
	_ = _49_x
	return _49_x
}
func (_static *CompanionStruct_Default___) UINT16__LIMIT() _dafny.Int {
	return _dafny.IntOfInt64(65536)
}
func (_static *CompanionStruct_Default___) UINT32__LIMIT() _dafny.Int {
	return _dafny.IntOfInt64(4294967296)
}
func (_static *CompanionStruct_Default___) UINT64__LIMIT() _dafny.Int {
	return _dafny.IntOfString("18446744073709551616")
}
func (_static *CompanionStruct_Default___) INT32__MAX__LIMIT() _dafny.Int {
	return _dafny.IntOfInt64(2147483648)
}
func (_static *CompanionStruct_Default___) INT64__MAX__LIMIT() _dafny.Int {
	return _dafny.IntOfString("9223372036854775808")
}

// End of class Default__

// Definition of class Uint8
type Uint8 struct {
}

func New_Uint8_() *Uint8 {
	_this := Uint8{}

	return &_this
}

type CompanionStruct_Uint8_ struct {
}

var Companion_Uint8_ = CompanionStruct_Uint8_{}

func (*Uint8) String() string {
	return "StandardLibrary_mUInt.Uint8"
}
func (_this *Uint8) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Uint8{}

func (_this *CompanionStruct_Uint8_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint8(0), false
		}
		return next.(_dafny.Int).Uint8(), true
	}
}

// End of class Uint8

func Type_Uint8_() _dafny.TypeDescriptor {
	return type_Uint8_{}
}

type type_Uint8_ struct {
}

func (_this type_Uint8_) Default() interface{} {
	return uint8(0)
}

func (_this type_Uint8_) String() string {
	return "StandardLibrary_mUInt.Uint8"
}

// Definition of class Uint16
type Uint16 struct {
}

func New_Uint16_() *Uint16 {
	_this := Uint16{}

	return &_this
}

type CompanionStruct_Uint16_ struct {
}

var Companion_Uint16_ = CompanionStruct_Uint16_{}

func (*Uint16) String() string {
	return "StandardLibrary_mUInt.Uint16"
}
func (_this *Uint16) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Uint16{}

func (_this *CompanionStruct_Uint16_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint16(0), false
		}
		return next.(_dafny.Int).Uint16(), true
	}
}

// End of class Uint16

func Type_Uint16_() _dafny.TypeDescriptor {
	return type_Uint16_{}
}

type type_Uint16_ struct {
}

func (_this type_Uint16_) Default() interface{} {
	return uint16(0)
}

func (_this type_Uint16_) String() string {
	return "StandardLibrary_mUInt.Uint16"
}

// Definition of class Uint32
type Uint32 struct {
}

func New_Uint32_() *Uint32 {
	_this := Uint32{}

	return &_this
}

type CompanionStruct_Uint32_ struct {
}

var Companion_Uint32_ = CompanionStruct_Uint32_{}

func (*Uint32) String() string {
	return "StandardLibrary_mUInt.Uint32"
}
func (_this *Uint32) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Uint32{}

func (_this *CompanionStruct_Uint32_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint32(0), false
		}
		return next.(_dafny.Int).Uint32(), true
	}
}

// End of class Uint32

func Type_Uint32_() _dafny.TypeDescriptor {
	return type_Uint32_{}
}

type type_Uint32_ struct {
}

func (_this type_Uint32_) Default() interface{} {
	return uint32(0)
}

func (_this type_Uint32_) String() string {
	return "StandardLibrary_mUInt.Uint32"
}

// Definition of class Uint64
type Uint64 struct {
}

func New_Uint64_() *Uint64 {
	_this := Uint64{}

	return &_this
}

type CompanionStruct_Uint64_ struct {
}

var Companion_Uint64_ = CompanionStruct_Uint64_{}

func (*Uint64) String() string {
	return "StandardLibrary_mUInt.Uint64"
}
func (_this *Uint64) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Uint64{}

func (_this *CompanionStruct_Uint64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint64(0), false
		}
		return next.(_dafny.Int).Uint64(), true
	}
}

// End of class Uint64

func Type_Uint64_() _dafny.TypeDescriptor {
	return type_Uint64_{}
}

type type_Uint64_ struct {
}

func (_this type_Uint64_) Default() interface{} {
	return uint64(0)
}

func (_this type_Uint64_) String() string {
	return "StandardLibrary_mUInt.Uint64"
}

// Definition of class Int32
type Int32 struct {
}

func New_Int32_() *Int32 {
	_this := Int32{}

	return &_this
}

type CompanionStruct_Int32_ struct {
}

var Companion_Int32_ = CompanionStruct_Int32_{}

func (*Int32) String() string {
	return "StandardLibrary_mUInt.Int32"
}
func (_this *Int32) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Int32{}

func (_this *CompanionStruct_Int32_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return int32(0), false
		}
		return next.(_dafny.Int).Int32(), true
	}
}

// End of class Int32

func Type_Int32_() _dafny.TypeDescriptor {
	return type_Int32_{}
}

type type_Int32_ struct {
}

func (_this type_Int32_) Default() interface{} {
	return int32(0)
}

func (_this type_Int32_) String() string {
	return "StandardLibrary_mUInt.Int32"
}

// Definition of class Int64
type Int64 struct {
}

func New_Int64_() *Int64 {
	_this := Int64{}

	return &_this
}

type CompanionStruct_Int64_ struct {
}

var Companion_Int64_ = CompanionStruct_Int64_{}

func (*Int64) String() string {
	return "StandardLibrary_mUInt.Int64"
}
func (_this *Int64) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Int64{}

func (_this *CompanionStruct_Int64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return int64(0), false
		}
		return next.(_dafny.Int).Int64(), true
	}
}

// End of class Int64

func Type_Int64_() _dafny.TypeDescriptor {
	return type_Int64_{}
}

type type_Int64_ struct {
}

func (_this type_Int64_) Default() interface{} {
	return int64(0)
}

func (_this type_Int64_) String() string {
	return "StandardLibrary_mUInt.Int64"
}

// Definition of class PosInt64
type PosInt64 struct {
}

func New_PosInt64_() *PosInt64 {
	_this := PosInt64{}

	return &_this
}

type CompanionStruct_PosInt64_ struct {
}

var Companion_PosInt64_ = CompanionStruct_PosInt64_{}

func (*PosInt64) String() string {
	return "StandardLibrary_mUInt.PosInt64"
}
func (_this *PosInt64) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &PosInt64{}

func (_this *CompanionStruct_PosInt64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
	iter := _dafny.IntegerRange(lo, hi)
	return func() (interface{}, bool) {
		next, ok := iter()
		if !ok {
			return uint64(0), false
		}
		return next.(_dafny.Int).Uint64(), true
	}
}
func (_this *CompanionStruct_PosInt64_) Witness() uint64 {
	return (_dafny.One).Uint64()
}

// End of class PosInt64

func Type_PosInt64_() _dafny.TypeDescriptor {
	return type_PosInt64_{}
}

type type_PosInt64_ struct {
}

func (_this type_PosInt64_) Default() interface{} {
	return Companion_PosInt64_.Witness()
}

func (_this type_PosInt64_) String() string {
	return "StandardLibrary_mUInt.PosInt64"
}

// Definition of class Seq16
type Seq16 struct {
}

func New_Seq16_() *Seq16 {
	_this := Seq16{}

	return &_this
}

type CompanionStruct_Seq16_ struct {
}

var Companion_Seq16_ = CompanionStruct_Seq16_{}

func (*Seq16) String() string {
	return "StandardLibrary_mUInt.Seq16"
}

// End of class Seq16

func Type_Seq16_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
	return type_Seq16_{Type_T_}
}

type type_Seq16_ struct {
	Type_T_ _dafny.TypeDescriptor
}

func (_this type_Seq16_) Default() interface{} {
	return _dafny.EmptySeq
}

func (_this type_Seq16_) String() string {
	return "StandardLibrary_mUInt.Seq16"
}

// Definition of class Seq32
type Seq32 struct {
}

func New_Seq32_() *Seq32 {
	_this := Seq32{}

	return &_this
}

type CompanionStruct_Seq32_ struct {
}

var Companion_Seq32_ = CompanionStruct_Seq32_{}

func (*Seq32) String() string {
	return "StandardLibrary_mUInt.Seq32"
}

// End of class Seq32

func Type_Seq32_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
	return type_Seq32_{Type_T_}
}

type type_Seq32_ struct {
	Type_T_ _dafny.TypeDescriptor
}

func (_this type_Seq32_) Default() interface{} {
	return _dafny.EmptySeq
}

func (_this type_Seq32_) String() string {
	return "StandardLibrary_mUInt.Seq32"
}

// Definition of class Seq64
type Seq64 struct {
}

func New_Seq64_() *Seq64 {
	_this := Seq64{}

	return &_this
}

type CompanionStruct_Seq64_ struct {
}

var Companion_Seq64_ = CompanionStruct_Seq64_{}

func (*Seq64) String() string {
	return "StandardLibrary_mUInt.Seq64"
}

// End of class Seq64

func Type_Seq64_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
	return type_Seq64_{Type_T_}
}

type type_Seq64_ struct {
	Type_T_ _dafny.TypeDescriptor
}

func (_this type_Seq64_) Default() interface{} {
	return _dafny.EmptySeq
}

func (_this type_Seq64_) String() string {
	return "StandardLibrary_mUInt.Seq64"
}
