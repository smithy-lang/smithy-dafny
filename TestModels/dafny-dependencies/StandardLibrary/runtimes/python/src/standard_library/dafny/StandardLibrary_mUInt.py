import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers

assert "StandardLibrary_mUInt" == __name__
StandardLibrary_mUInt = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def UInt8Less(a, b):
        return (a) < (b)

    @staticmethod
    def HasUint16Len(s):
        return (len(s)) < (StandardLibrary_mUInt.default__.UINT16__LIMIT)

    @staticmethod
    def HasUint32Len(s):
        return (len(s)) < (StandardLibrary_mUInt.default__.UINT32__LIMIT)

    @staticmethod
    def HasUint64Len(s):
        return (len(s)) < (StandardLibrary_mUInt.default__.UINT64__LIMIT)

    @staticmethod
    def UInt16ToSeq(x):
        d_16_b0_ = _dafny.euclidian_division(x, 256)
        d_17_b1_ = _dafny.euclidian_modulus(x, 256)
        return _dafny.Seq([d_16_b0_, d_17_b1_])

    @staticmethod
    def SeqToUInt16(s):
        d_18_x0_ = ((s)[0]) * (256)
        return (d_18_x0_) + ((s)[1])

    @staticmethod
    def UInt32ToSeq(x):
        d_19_b0_ = _dafny.euclidian_division(x, 16777216)
        d_20_x0_ = (x) - ((d_19_b0_) * (16777216))
        d_21_b1_ = _dafny.euclidian_division(d_20_x0_, 65536)
        d_22_x1_ = (d_20_x0_) - ((d_21_b1_) * (65536))
        d_23_b2_ = _dafny.euclidian_division(d_22_x1_, 256)
        d_24_b3_ = _dafny.euclidian_modulus(d_22_x1_, 256)
        return _dafny.Seq([d_19_b0_, d_21_b1_, d_23_b2_, d_24_b3_])

    @staticmethod
    def SeqToUInt32(s):
        d_25_x0_ = ((s)[0]) * (16777216)
        d_26_x1_ = (d_25_x0_) + (((s)[1]) * (65536))
        d_27_x2_ = (d_26_x1_) + (((s)[2]) * (256))
        return (d_27_x2_) + ((s)[3])

    @staticmethod
    def UInt64ToSeq(x):
        d_28_b0_ = _dafny.euclidian_division(x, 72057594037927936)
        d_29_x0_ = (x) - ((d_28_b0_) * (72057594037927936))
        d_30_b1_ = _dafny.euclidian_division(d_29_x0_, 281474976710656)
        d_31_x1_ = (d_29_x0_) - ((d_30_b1_) * (281474976710656))
        d_32_b2_ = _dafny.euclidian_division(d_31_x1_, 1099511627776)
        d_33_x2_ = (d_31_x1_) - ((d_32_b2_) * (1099511627776))
        d_34_b3_ = _dafny.euclidian_division(d_33_x2_, 4294967296)
        d_35_x3_ = (d_33_x2_) - ((d_34_b3_) * (4294967296))
        d_36_b4_ = _dafny.euclidian_division(d_35_x3_, 16777216)
        d_37_x4_ = (d_35_x3_) - ((d_36_b4_) * (16777216))
        d_38_b5_ = _dafny.euclidian_division(d_37_x4_, 65536)
        d_39_x5_ = (d_37_x4_) - ((d_38_b5_) * (65536))
        d_40_b6_ = _dafny.euclidian_division(d_39_x5_, 256)
        d_41_b7_ = _dafny.euclidian_modulus(d_39_x5_, 256)
        return _dafny.Seq([d_28_b0_, d_30_b1_, d_32_b2_, d_34_b3_, d_36_b4_, d_38_b5_, d_40_b6_, d_41_b7_])

    @staticmethod
    def SeqToUInt64(s):
        d_42_x0_ = ((s)[0]) * (72057594037927936)
        d_43_x1_ = (d_42_x0_) + (((s)[1]) * (281474976710656))
        d_44_x2_ = (d_43_x1_) + (((s)[2]) * (1099511627776))
        d_45_x3_ = (d_44_x2_) + (((s)[3]) * (4294967296))
        d_46_x4_ = (d_45_x3_) + (((s)[4]) * (16777216))
        d_47_x5_ = (d_46_x4_) + (((s)[5]) * (65536))
        d_48_x6_ = (d_47_x5_) + (((s)[6]) * (256))
        d_49_x_ = (d_48_x6_) + ((s)[7])
        return d_49_x_

    @_dafny.classproperty
    def UINT16__LIMIT(instance):
        return 65536
    @_dafny.classproperty
    def UINT32__LIMIT(instance):
        return 4294967296
    @_dafny.classproperty
    def UINT64__LIMIT(instance):
        return 18446744073709551616
    @_dafny.classproperty
    def INT32__MAX__LIMIT(instance):
        return 2147483648
    @_dafny.classproperty
    def INT64__MAX__LIMIT(instance):
        return 9223372036854775808

class uint8:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class uint16:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class uint32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class uint64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class int32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class int64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class posInt64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return 1

class seq16:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class seq32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class seq64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})
