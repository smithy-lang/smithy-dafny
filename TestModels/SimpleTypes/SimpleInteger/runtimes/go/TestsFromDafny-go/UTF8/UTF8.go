// Package UTF8
// Dafny module UTF8 compiled into Go

package UTF8

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
	return "UTF8.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) CreateEncodeSuccess(bytes _dafny.Sequence) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(bytes)
}
func (_static *CompanionStruct_Default___) CreateEncodeFailure(error_ _dafny.Sequence) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}
func (_static *CompanionStruct_Default___) CreateDecodeSuccess(s _dafny.Sequence) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(s)
}
func (_static *CompanionStruct_Default___) CreateDecodeFailure(error_ _dafny.Sequence) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}
func (_static *CompanionStruct_Default___) IsASCIIString(s _dafny.Sequence) bool {
	var _hresult bool = false
	_ = _hresult
	var _hi0 _dafny.Int = _dafny.IntOfUint32((s).Cardinality())
	_ = _hi0
	for _72_i := _dafny.Zero; _72_i.Cmp(_hi0) < 0; _72_i = _72_i.Plus(_dafny.One) {
		if !((_dafny.IntOfInt32(rune((s).Select((_72_i).Uint32()).(_dafny.CodePoint)))).Cmp(_dafny.IntOfInt64(128)) < 0) {
			_hresult = false
			return _hresult
		}
	}
	_hresult = true
	return _hresult
	return _hresult
}
func (_static *CompanionStruct_Default___) EncodeAscii(s _dafny.Sequence) _dafny.Sequence {
	var _73___accumulator _dafny.Sequence = _dafny.SeqOf()
	_ = _73___accumulator
	goto TAIL_CALL_START
TAIL_CALL_START:
	if (_dafny.IntOfUint32((s).Cardinality())).Sign() == 0 {
		return _dafny.Companion_Sequence_.Concatenate(_73___accumulator, _dafny.SeqOf())
	} else {
		var _74_x _dafny.Sequence = _dafny.SeqOf(uint8((s).Select(0).(_dafny.CodePoint)))
		_ = _74_x
		_73___accumulator = _dafny.Companion_Sequence_.Concatenate(_73___accumulator, _74_x)
		var _in11 _dafny.Sequence = (s).Drop(1)
		_ = _in11
		s = _in11
		goto TAIL_CALL_START
	}
}
func (_static *CompanionStruct_Default___) Uses1Byte(s _dafny.Sequence) bool {
	return ((uint8(0)) <= ((s).Select(0).(uint8))) && (((s).Select(0).(uint8)) <= (uint8(127)))
}
func (_static *CompanionStruct_Default___) Uses2Bytes(s _dafny.Sequence) bool {
	return (((uint8(194)) <= ((s).Select(0).(uint8))) && (((s).Select(0).(uint8)) <= (uint8(223)))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))
}
func (_static *CompanionStruct_Default___) Uses3Bytes(s _dafny.Sequence) bool {
	return (((((((s).Select(0).(uint8)) == (uint8(224))) && (((uint8(160)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191))))) || (((((uint8(225)) <= ((s).Select(0).(uint8))) && (((s).Select(0).(uint8)) <= (uint8(236)))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191)))))) || (((((s).Select(0).(uint8)) == (uint8(237))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(159))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191)))))) || (((((uint8(238)) <= ((s).Select(0).(uint8))) && (((s).Select(0).(uint8)) <= (uint8(239)))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191)))))
}
func (_static *CompanionStruct_Default___) Uses4Bytes(s _dafny.Sequence) bool {
	return (((((((s).Select(0).(uint8)) == (uint8(240))) && (((uint8(144)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(3).(uint8))) && (((s).Select(3).(uint8)) <= (uint8(191))))) || ((((((uint8(241)) <= ((s).Select(0).(uint8))) && (((s).Select(0).(uint8)) <= (uint8(243)))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(3).(uint8))) && (((s).Select(3).(uint8)) <= (uint8(191)))))) || ((((((s).Select(0).(uint8)) == (uint8(244))) && (((uint8(128)) <= ((s).Select(1).(uint8))) && (((s).Select(1).(uint8)) <= (uint8(143))))) && (((uint8(128)) <= ((s).Select(2).(uint8))) && (((s).Select(2).(uint8)) <= (uint8(191))))) && (((uint8(128)) <= ((s).Select(3).(uint8))) && (((s).Select(3).(uint8)) <= (uint8(191)))))
}
func (_static *CompanionStruct_Default___) ValidUTF8Range(a _dafny.Sequence, lo _dafny.Int, hi _dafny.Int) bool {
	goto TAIL_CALL_START
TAIL_CALL_START:
	if (lo).Cmp(hi) == 0 {
		return true
	} else {
		var _75_r _dafny.Sequence = (a).Subsequence((lo).Uint32(), (hi).Uint32())
		_ = _75_r
		if Companion_Default___.Uses1Byte(_75_r) {
			var _in12 _dafny.Sequence = a
			_ = _in12
			var _in13 _dafny.Int = (lo).Plus(_dafny.One)
			_ = _in13
			var _in14 _dafny.Int = hi
			_ = _in14
			a = _in12
			lo = _in13
			hi = _in14
			goto TAIL_CALL_START
		} else if ((_dafny.IntOfInt64(2)).Cmp(_dafny.IntOfUint32((_75_r).Cardinality())) <= 0) && (Companion_Default___.Uses2Bytes(_75_r)) {
			var _in15 _dafny.Sequence = a
			_ = _in15
			var _in16 _dafny.Int = (lo).Plus(_dafny.IntOfInt64(2))
			_ = _in16
			var _in17 _dafny.Int = hi
			_ = _in17
			a = _in15
			lo = _in16
			hi = _in17
			goto TAIL_CALL_START
		} else if ((_dafny.IntOfInt64(3)).Cmp(_dafny.IntOfUint32((_75_r).Cardinality())) <= 0) && (Companion_Default___.Uses3Bytes(_75_r)) {
			var _in18 _dafny.Sequence = a
			_ = _in18
			var _in19 _dafny.Int = (lo).Plus(_dafny.IntOfInt64(3))
			_ = _in19
			var _in20 _dafny.Int = hi
			_ = _in20
			a = _in18
			lo = _in19
			hi = _in20
			goto TAIL_CALL_START
		} else if ((_dafny.IntOfInt64(4)).Cmp(_dafny.IntOfUint32((_75_r).Cardinality())) <= 0) && (Companion_Default___.Uses4Bytes(_75_r)) {
			var _in21 _dafny.Sequence = a
			_ = _in21
			var _in22 _dafny.Int = (lo).Plus(_dafny.IntOfInt64(4))
			_ = _in22
			var _in23 _dafny.Int = hi
			_ = _in23
			a = _in21
			lo = _in22
			hi = _in23
			goto TAIL_CALL_START
		} else {
			return false
		}
	}
}
func (_static *CompanionStruct_Default___) ValidUTF8Seq(s _dafny.Sequence) bool {
	return Companion_Default___.ValidUTF8Range(s, _dafny.Zero, _dafny.IntOfUint32((s).Cardinality()))
}

// End of class Default__

// Definition of class ValidUTF8Bytes
type ValidUTF8Bytes struct {
}

func New_ValidUTF8Bytes_() *ValidUTF8Bytes {
	_this := ValidUTF8Bytes{}

	return &_this
}

type CompanionStruct_ValidUTF8Bytes_ struct {
}

var Companion_ValidUTF8Bytes_ = CompanionStruct_ValidUTF8Bytes_{}

func (*ValidUTF8Bytes) String() string {
	return "UTF8.ValidUTF8Bytes"
}
func (_this *CompanionStruct_ValidUTF8Bytes_) Witness() _dafny.Sequence {
	return _dafny.SeqOf()
}

// End of class ValidUTF8Bytes

func Type_ValidUTF8Bytes_() _dafny.TypeDescriptor {
	return type_ValidUTF8Bytes_{}
}

type type_ValidUTF8Bytes_ struct {
}

func (_this type_ValidUTF8Bytes_) Default() interface{} {
	return Companion_ValidUTF8Bytes_.Witness()
}

func (_this type_ValidUTF8Bytes_) String() string {
	return "UTF8.ValidUTF8Bytes"
}
func (_this *CompanionStruct_ValidUTF8Bytes_) Is_(__source _dafny.Sequence) bool {
	var _76_i _dafny.Sequence = (__source)
	_ = _76_i
	return Companion_Default___.ValidUTF8Seq(_76_i)
}
