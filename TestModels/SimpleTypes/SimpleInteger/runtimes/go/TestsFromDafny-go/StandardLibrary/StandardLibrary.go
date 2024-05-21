// Package StandardLibrary
// Dafny module StandardLibrary compiled into Go

package StandardLibrary

import (
	os "os"

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
	return "StandardLibrary.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Join(ss _dafny.Sequence, joiner _dafny.Sequence) _dafny.Sequence {
	var _54___accumulator _dafny.Sequence = _dafny.SeqOf()
	_ = _54___accumulator
	goto TAIL_CALL_START
TAIL_CALL_START:
	if (_dafny.IntOfUint32((ss).Cardinality())).Cmp(_dafny.One) == 0 {
		return _dafny.Companion_Sequence_.Concatenate(_54___accumulator, (ss).Select(0).(_dafny.Sequence))
	} else {
		_54___accumulator = _dafny.Companion_Sequence_.Concatenate(_54___accumulator, _dafny.Companion_Sequence_.Concatenate((ss).Select(0).(_dafny.Sequence), joiner))
		var _in0 _dafny.Sequence = (ss).Drop(1)
		_ = _in0
		var _in1 _dafny.Sequence = joiner
		_ = _in1
		ss = _in0
		joiner = _in1
		goto TAIL_CALL_START
	}
}
func (_static *CompanionStruct_Default___) Split(s _dafny.Sequence, delim interface{}) _dafny.Sequence {
	var _55___accumulator _dafny.Sequence = _dafny.SeqOf()
	_ = _55___accumulator
	goto TAIL_CALL_START
TAIL_CALL_START:
	var _56_i Wrappers.Option = Companion_Default___.FindIndexMatching(s, delim, _dafny.Zero)
	_ = _56_i
	if (_56_i).Is_Some() {
		_55___accumulator = _dafny.Companion_Sequence_.Concatenate(_55___accumulator, _dafny.SeqOf((s).Take(((_56_i).Dtor_value().(_dafny.Int)).Uint32())))
		var _in2 _dafny.Sequence = (s).Drop((((_56_i).Dtor_value().(_dafny.Int)).Plus(_dafny.One)).Uint32())
		_ = _in2
		var _in3 interface{} = delim
		_ = _in3
		s = _in2
		delim = _in3
		goto TAIL_CALL_START
	} else {
		return _dafny.Companion_Sequence_.Concatenate(_55___accumulator, _dafny.SeqOf(s))
	}
}
func (_static *CompanionStruct_Default___) SplitOnce(s _dafny.Sequence, delim interface{}) _dafny.Tuple {
	var _57_i Wrappers.Option = Companion_Default___.FindIndexMatching(s, delim, _dafny.Zero)
	_ = _57_i
	return _dafny.TupleOf((s).Take(((_57_i).Dtor_value().(_dafny.Int)).Uint32()), (s).Drop((((_57_i).Dtor_value().(_dafny.Int)).Plus(_dafny.One)).Uint32()))
}
func (_static *CompanionStruct_Default___) SplitOnce_q(s _dafny.Sequence, delim interface{}) Wrappers.Option {
	var _58_valueOrError0 Wrappers.Option = Companion_Default___.FindIndexMatching(s, delim, _dafny.Zero)
	_ = _58_valueOrError0
	if (_58_valueOrError0).IsFailure() {
		return (_58_valueOrError0).PropagateFailure()
	} else {
		var _59_i _dafny.Int = (_58_valueOrError0).Extract().(_dafny.Int)
		_ = _59_i
		return Wrappers.Companion_Option_.Create_Some_(_dafny.TupleOf((s).Take((_59_i).Uint32()), (s).Drop(((_59_i).Plus(_dafny.One)).Uint32())))
	}
}
func (_static *CompanionStruct_Default___) FindIndexMatching(s _dafny.Sequence, c interface{}, i _dafny.Int) Wrappers.Option {
	return Companion_Default___.FindIndex(s, func(coer0 func(interface{}) bool) func(interface{}) bool {
		return func(arg0 interface{}) bool {
			return coer0(arg0)
		}
	}((func(_60_c interface{}) func(interface{}) bool {
		return func(_61_x interface{}) bool {
			return _dafny.AreEqual(_61_x, _60_c)
		}
	})(c)), i)
}
func (_static *CompanionStruct_Default___) FindIndex(s _dafny.Sequence, f func(interface{}) bool, i _dafny.Int) Wrappers.Option {
	goto TAIL_CALL_START
TAIL_CALL_START:
	if (i).Cmp(_dafny.IntOfUint32((s).Cardinality())) == 0 {
		return Wrappers.Companion_Option_.Create_None_()
	} else if (f)((s).Select((i).Uint32()).(interface{})) {
		return Wrappers.Companion_Option_.Create_Some_(i)
	} else {
		var _in4 _dafny.Sequence = s
		_ = _in4
		var _in5 func(interface{}) bool = f
		_ = _in5
		var _in6 _dafny.Int = (i).Plus(_dafny.One)
		_ = _in6
		s = _in4
		f = _in5
		i = _in6
		goto TAIL_CALL_START
	}
}
func (_static *CompanionStruct_Default___) Filter(s _dafny.Sequence, f func(interface{}) bool) _dafny.Sequence {
	var _62___accumulator _dafny.Sequence = _dafny.SeqOf()
	_ = _62___accumulator
	goto TAIL_CALL_START
TAIL_CALL_START:
	if (_dafny.IntOfUint32((s).Cardinality())).Sign() == 0 {
		return _dafny.Companion_Sequence_.Concatenate(_62___accumulator, _dafny.SeqOf())
	} else if (f)((s).Select(0).(interface{})) {
		_62___accumulator = _dafny.Companion_Sequence_.Concatenate(_62___accumulator, _dafny.SeqOf((s).Select(0).(interface{})))
		var _in7 _dafny.Sequence = (s).Drop(1)
		_ = _in7
		var _in8 func(interface{}) bool = f
		_ = _in8
		s = _in7
		f = _in8
		goto TAIL_CALL_START
	} else {
		var _in9 _dafny.Sequence = (s).Drop(1)
		_ = _in9
		var _in10 func(interface{}) bool = f
		_ = _in10
		s = _in9
		f = _in10
		goto TAIL_CALL_START
	}
}
func (_static *CompanionStruct_Default___) Min(a _dafny.Int, b _dafny.Int) _dafny.Int {
	if (a).Cmp(b) < 0 {
		return a
	} else {
		return b
	}
}
func (_static *CompanionStruct_Default___) Fill(value interface{}, n _dafny.Int) _dafny.Sequence {
	return _dafny.SeqCreate((n).Uint32(), func(coer1 func(_dafny.Int) interface{}) func(_dafny.Int) interface{} {
		return func(arg1 _dafny.Int) interface{} {
			return coer1(arg1)
		}
	}((func(_63_value interface{}) func(_dafny.Int) interface{} {
		return func(_64___v0 _dafny.Int) interface{} {
			return _63_value
		}
	})(value)))
}
func (_static *CompanionStruct_Default___) SeqToArray(s _dafny.Sequence) _dafny.Array {
	var a _dafny.Array = _dafny.NewArrayWithValue(nil, _dafny.IntOf(0))
	_ = a
	var _len0_0 _dafny.Int = _dafny.IntOfUint32((s).Cardinality())
	_ = _len0_0
	var _nw0 _dafny.Array
	_ = _nw0
	if _len0_0.Cmp(_dafny.Zero) == 0 {
		_nw0 = _dafny.NewArray(_len0_0)
	} else {
		var _init0 func(_dafny.Int) interface{} = (func(_65_s _dafny.Sequence) func(_dafny.Int) interface{} {
			return func(_66_i _dafny.Int) interface{} {
				return (_65_s).Select((_66_i).Uint32()).(interface{})
			}
		})(s)
		_ = _init0
		var _element0_0 = _init0(_dafny.Zero)
		_ = _element0_0
		_nw0 = _dafny.NewArrayFromExample(_element0_0, nil, _len0_0)
		(_nw0).ArraySet1(_element0_0, 0)
		var _nativeLen0_0 = (_len0_0).Int()
		_ = _nativeLen0_0
		for _i0_0 := 1; _i0_0 < _nativeLen0_0; _i0_0++ {
			(_nw0).ArraySet1(_init0(_dafny.IntOf(_i0_0)), _i0_0)
		}
	}
	a = _nw0
	return a
}
func (_static *CompanionStruct_Default___) LexicographicLessOrEqual(a _dafny.Sequence, b _dafny.Sequence, less func(interface{}, interface{}) bool) bool {
	return _dafny.Quantifier(_dafny.IntegerRange(_dafny.Zero, (_dafny.IntOfUint32((a).Cardinality())).Plus(_dafny.One)), false, func(_exists_var_0 _dafny.Int) bool {
		var _67_k _dafny.Int
		_67_k = interface{}(_exists_var_0).(_dafny.Int)
		return (((_67_k).Sign() != -1) && ((_67_k).Cmp(_dafny.IntOfUint32((a).Cardinality())) <= 0)) && (Companion_Default___.LexicographicLessOrEqualAux(a, b, func(coer2 func(interface{}, interface{}) bool) func(interface{}, interface{}) bool {
			return func(arg2 interface{}, arg3 interface{}) bool {
				return coer2(arg2, arg3)
			}
		}(less), _67_k))
	})
}
func (_static *CompanionStruct_Default___) LexicographicLessOrEqualAux(a _dafny.Sequence, b _dafny.Sequence, less func(interface{}, interface{}) bool, lengthOfCommonPrefix _dafny.Int) bool {
	return (((lengthOfCommonPrefix).Cmp(_dafny.IntOfUint32((b).Cardinality())) <= 0) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.Zero, lengthOfCommonPrefix), true, func(_forall_var_0 _dafny.Int) bool {
		var _68_i _dafny.Int
		_68_i = interface{}(_forall_var_0).(_dafny.Int)
		return !(((_68_i).Sign() != -1) && ((_68_i).Cmp(lengthOfCommonPrefix) < 0)) || (_dafny.AreEqual((a).Select((_68_i).Uint32()).(interface{}), (b).Select((_68_i).Uint32()).(interface{})))
	}))) && (((lengthOfCommonPrefix).Cmp(_dafny.IntOfUint32((a).Cardinality())) == 0) || (((lengthOfCommonPrefix).Cmp(_dafny.IntOfUint32((b).Cardinality())) < 0) && ((less)((a).Select((lengthOfCommonPrefix).Uint32()).(interface{}), (b).Select((lengthOfCommonPrefix).Uint32()).(interface{})))))
}
func (_static *CompanionStruct_Default___) SetToOrderedSequence(s _dafny.Set, less func(interface{}, interface{}) bool) _dafny.Sequence {
	var _69___accumulator _dafny.Sequence = _dafny.SeqOf()
	_ = _69___accumulator
	goto TAIL_CALL_START
TAIL_CALL_START:
	var _pat_let_tv0 = s
	_ = _pat_let_tv0
	var _pat_let_tv1 = less
	_ = _pat_let_tv1
	if (s).Equals(_dafny.SetOf()) {
		return _dafny.Companion_Sequence_.Concatenate(_69___accumulator, _dafny.SeqOf())
	} else {
		return func(_let_dummy_0 int) _dafny.Sequence {
			var _70_a _dafny.Sequence = _dafny.EmptySeq
			_ = _70_a
			{
				for _iter0 := _dafny.Iterate((s).Elements()); ; {
					_assign_such_that_0, _ok0 := _iter0()
					if !_ok0 {
						break
					}
					_70_a = interface{}(_assign_such_that_0).(_dafny.Sequence)
					if ((s).Contains(_70_a)) && (Companion_Default___.IsMinimum(_70_a, s, func(coer3 func(interface{}, interface{}) bool) func(interface{}, interface{}) bool {
						return func(arg4 interface{}, arg5 interface{}) bool {
							return coer3(arg4, arg5)
						}
					}(less))) {
						goto L_ASSIGN_SUCH_THAT_0
					}
				}
				panic("assign-such-that search produced no value (line 369)")
				goto L_ASSIGN_SUCH_THAT_0
			}
		L_ASSIGN_SUCH_THAT_0:
			return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(_70_a), Companion_Default___.SetToOrderedSequence((_pat_let_tv0).Difference(_dafny.SetOf(_70_a)), _pat_let_tv1))
		}(0)
	}
}
func (_static *CompanionStruct_Default___) IsMinimum(a _dafny.Sequence, s _dafny.Set, less func(interface{}, interface{}) bool) bool {
	return ((s).Contains(a)) && (_dafny.Quantifier((s).Elements(), true, func(_forall_var_1 _dafny.Sequence) bool {
		var _71_z _dafny.Sequence
		_71_z = interface{}(_forall_var_1).(_dafny.Sequence)
		return !((s).Contains(_71_z)) || (Companion_Default___.LexicographicLessOrEqual(a, _71_z, func(coer4 func(interface{}, interface{}) bool) func(interface{}, interface{}) bool {
			return func(arg6 interface{}, arg7 interface{}) bool {
				return coer4(arg6, arg7)
			}
		}(less)))
	}))
}

// End of class Default__
