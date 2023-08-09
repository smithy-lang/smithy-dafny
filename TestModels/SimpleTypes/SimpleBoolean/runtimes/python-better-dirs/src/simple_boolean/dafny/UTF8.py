import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

# from . import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary

# assert "UTF8" == __name__
UTF8 = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsASCIIString(s):
        def lambda7_(forall_var_2_):
            d_67_i_: int = forall_var_2_
            return not (((0) <= (d_67_i_)) and ((d_67_i_) < (len(s)))) or ((ord((s)[d_67_i_])) < (128))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda7_)

    @staticmethod
    def EncodeAscii(s):
        d_68___accumulator_ = _dafny.Seq([])
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (d_68___accumulator_) + (_dafny.Seq([]))
                elif True:
                    d_69_x_ = _dafny.Seq([ord((s)[0])])
                    d_68___accumulator_ = (d_68___accumulator_) + (d_69_x_)
                    in11_ = _dafny.Seq((s)[1::])
                    s = in11_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Uses1Byte(s):
        return ((0) <= ((s)[0])) and (((s)[0]) <= (127))

    @staticmethod
    def Uses2Bytes(s):
        return (((194) <= ((s)[0])) and (((s)[0]) <= (223))) and (((128) <= ((s)[1])) and (((s)[1]) <= (191)))

    @staticmethod
    def Uses3Bytes(s):
        return (((((((s)[0]) == (224)) and (((160) <= ((s)[1])) and (((s)[1]) <= (191)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191)))) or (((((225) <= ((s)[0])) and (((s)[0]) <= (236))) and (((128) <= ((s)[1])) and (((s)[1]) <= (191)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191))))) or (((((s)[0]) == (237)) and (((128) <= ((s)[1])) and (((s)[1]) <= (159)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191))))) or (((((238) <= ((s)[0])) and (((s)[0]) <= (239))) and (((128) <= ((s)[1])) and (((s)[1]) <= (191)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191))))

    @staticmethod
    def Uses4Bytes(s):
        return (((((((s)[0]) == (240)) and (((144) <= ((s)[1])) and (((s)[1]) <= (191)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191)))) and (((128) <= ((s)[3])) and (((s)[3]) <= (191)))) or ((((((241) <= ((s)[0])) and (((s)[0]) <= (243))) and (((128) <= ((s)[1])) and (((s)[1]) <= (191)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191)))) and (((128) <= ((s)[3])) and (((s)[3]) <= (191))))) or ((((((s)[0]) == (244)) and (((128) <= ((s)[1])) and (((s)[1]) <= (143)))) and (((128) <= ((s)[2])) and (((s)[2]) <= (191)))) and (((128) <= ((s)[3])) and (((s)[3]) <= (191))))

    @staticmethod
    def ValidUTF8Range(a, lo, hi):
        while True:
            with _dafny.label():
                if (lo) == (hi):
                    return True
                elif True:
                    d_70_r_ = _dafny.Seq((a)[lo:hi:])
                    if UTF8.default__.Uses1Byte(d_70_r_):
                        in12_ = a
                        in13_ = (lo) + (1)
                        in14_ = hi
                        a = in12_
                        lo = in13_
                        hi = in14_
                        raise _dafny.TailCall()
                    elif ((2) <= (len(d_70_r_))) and (UTF8.default__.Uses2Bytes(d_70_r_)):
                        in15_ = a
                        in16_ = (lo) + (2)
                        in17_ = hi
                        a = in15_
                        lo = in16_
                        hi = in17_
                        raise _dafny.TailCall()
                    elif ((3) <= (len(d_70_r_))) and (UTF8.default__.Uses3Bytes(d_70_r_)):
                        in18_ = a
                        in19_ = (lo) + (3)
                        in20_ = hi
                        a = in18_
                        lo = in19_
                        hi = in20_
                        raise _dafny.TailCall()
                    elif ((4) <= (len(d_70_r_))) and (UTF8.default__.Uses4Bytes(d_70_r_)):
                        in21_ = a
                        in22_ = (lo) + (4)
                        in23_ = hi
                        a = in21_
                        lo = in22_
                        hi = in23_
                        raise _dafny.TailCall()
                    elif True:
                        return False
                break

    @staticmethod
    def ValidUTF8Seq(s):
        return UTF8.default__.ValidUTF8Range(s, 0, len(s))


class ValidUTF8Bytes:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq([])
