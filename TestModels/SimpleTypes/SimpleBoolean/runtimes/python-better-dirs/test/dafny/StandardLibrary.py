import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt

# assert "StandardLibrary" == __name__
StandardLibrary = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Join(ss, joiner):
        d_50___accumulator_ = _dafny.Seq([])
        while True:
            with _dafny.label():
                if (len(ss)) == (1):
                    return (d_50___accumulator_) + ((ss)[0])
                elif True:
                    d_50___accumulator_ = (d_50___accumulator_) + (((ss)[0]) + (joiner))
                    in0_ = _dafny.Seq((ss)[1::])
                    in1_ = joiner
                    ss = in0_
                    joiner = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Split(s, delim):
        d_51___accumulator_ = _dafny.Seq([])
        while True:
            with _dafny.label():
                d_52_i_ = StandardLibrary.default__.FindIndexMatching(s, delim, 0)
                if (d_52_i_).is_Some:
                    d_51___accumulator_ = (d_51___accumulator_) + (_dafny.Seq([_dafny.Seq((s)[:(d_52_i_).value:])]))
                    in2_ = _dafny.Seq((s)[((d_52_i_).value) + (1)::])
                    in3_ = delim
                    s = in2_
                    delim = in3_
                    raise _dafny.TailCall()
                elif True:
                    return (d_51___accumulator_) + (_dafny.Seq([s]))
                break

    @staticmethod
    def SplitOnce(s, delim):
        d_53_i_ = StandardLibrary.default__.FindIndexMatching(s, delim, 0)
        return (_dafny.Seq((s)[:(d_53_i_).value:]), _dafny.Seq((s)[((d_53_i_).value) + (1)::]))

    @staticmethod
    def SplitOnce_q(s, delim):
        d_54_valueOrError0_ = StandardLibrary.default__.FindIndexMatching(s, delim, 0)
        if (d_54_valueOrError0_).IsFailure():
            return (d_54_valueOrError0_).PropagateFailure()
        elif True:
            d_55_i_ = (d_54_valueOrError0_).Extract()
            return Wrappers.Option_Some((_dafny.Seq((s)[:d_55_i_:]), _dafny.Seq((s)[(d_55_i_) + (1)::])))

    @staticmethod
    def FindIndexMatching(s, c, i):
        def lambda0_(d_56_c_):
            def lambda1_(d_57_x_):
                return (d_57_x_) == (d_56_c_)

            return lambda1_

        return StandardLibrary.default__.FindIndex(s, lambda0_(c), i)

    @staticmethod
    def FindIndex(s, f, i):
        while True:
            with _dafny.label():
                if (i) == (len(s)):
                    return Wrappers.Option_None()
                elif f((s)[i]):
                    return Wrappers.Option_Some(i)
                elif True:
                    in4_ = s
                    in5_ = f
                    in6_ = (i) + (1)
                    s = in4_
                    f = in5_
                    i = in6_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Filter(s, f):
        d_58___accumulator_ = _dafny.Seq([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_58___accumulator_) + (_dafny.Seq([]))
                elif f((s)[0]):
                    d_58___accumulator_ = (d_58___accumulator_) + (_dafny.Seq([(s)[0]]))
                    in7_ = _dafny.Seq((s)[1::])
                    in8_ = f
                    s = in7_
                    f = in8_
                    raise _dafny.TailCall()
                elif True:
                    in9_ = _dafny.Seq((s)[1::])
                    in10_ = f
                    s = in9_
                    f = in10_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Min(a, b):
        if (a) < (b):
            return a
        elif True:
            return b

    @staticmethod
    def Fill(value, n):
        return _dafny.Seq([value for d_59___v0_ in range(n)])

    @staticmethod
    def SeqToArray(s):
        a: _dafny.Array = _dafny.Array(None, 0)
        def lambda2_(d_60_s_):
            def lambda3_(d_61_i_):
                return (d_60_s_)[d_61_i_]

            return lambda3_

        init0_ = lambda2_(s)
        nw0_ = _dafny.Array(None, len(s))
        for i0_0_ in range(nw0_.length(0)):
            nw0_[i0_0_] = init0_(i0_0_)
        a = nw0_
        return a

    @staticmethod
    def LexicographicLessOrEqual(a, b, less):
        def lambda4_(exists_var_0_):
            d_62_k_: int = exists_var_0_
            return (((0) <= (d_62_k_)) and ((d_62_k_) <= (len(a)))) and (StandardLibrary.default__.LexicographicLessOrEqualAux(a, b, less, d_62_k_))

        return _dafny.quantifier(_dafny.IntegerRange(0, (len(a)) + (1)), False, lambda4_)

    @staticmethod
    def LexicographicLessOrEqualAux(a, b, less, lengthOfCommonPrefix):
        def lambda5_(forall_var_0_):
            d_63_i_: int = forall_var_0_
            return not (((0) <= (d_63_i_)) and ((d_63_i_) < (lengthOfCommonPrefix))) or (((a)[d_63_i_]) == ((b)[d_63_i_]))

        return (((lengthOfCommonPrefix) <= (len(b))) and (_dafny.quantifier(_dafny.IntegerRange(0, lengthOfCommonPrefix), True, lambda5_))) and (((lengthOfCommonPrefix) == (len(a))) or (((lengthOfCommonPrefix) < (len(b))) and (less((a)[lengthOfCommonPrefix], (b)[lengthOfCommonPrefix]))))

    @staticmethod
    def SetToOrderedSequence(s, less):
        d_64___accumulator_ = _dafny.Seq([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = s
                pat_let_tv1_ = less
                if (s) == (_dafny.Set({})):
                    return (d_64___accumulator_) + (_dafny.Seq([]))
                elif True:
                    def iife0_(_let_dummy_0):
                        d_65_a_: _dafny.Seq = None
                        with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                            assign_such_that_0_: _dafny.Seq
                            for assign_such_that_0_ in (s).Elements:
                                d_65_a_ = assign_such_that_0_
                                if ((d_65_a_) in (s)) and (StandardLibrary.default__.IsMinimum(d_65_a_, s, less)):
                                    raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                            raise Exception("assign-such-that search produced no value (line 369)")
                            pass
                        return (_dafny.Seq([d_65_a_])) + (StandardLibrary.default__.SetToOrderedSequence((pat_let_tv0_) - (_dafny.Set({d_65_a_})), pat_let_tv1_))
                    return iife0_(0)
                    
                break

    @staticmethod
    def IsMinimum(a, s, less):
        def lambda6_(forall_var_1_):
            d_66_z_: _dafny.Seq = forall_var_1_
            return not ((d_66_z_) in (s)) or (StandardLibrary.default__.LexicographicLessOrEqual(a, d_66_z_, less))

        return ((a) in (s)) and (_dafny.quantifier((s).Elements, True, lambda6_))

