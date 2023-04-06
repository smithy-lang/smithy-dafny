import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

assert "Wrappers_Compile" == __name__
Wrappers_Compile = sys.modules[__name__]

class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Wrappers_Compile.Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Wrappers_Compile.Option_Some)
    def ToResult(self):
        source0_ = self
        if source0_.is_None:
            return Wrappers_Compile.Result_Failure(_dafny.Seq("Option is None"))
        elif True:
            d_0___mcc_h0_ = source0_.value
            d_1_v_ = d_0___mcc_h0_
            return Wrappers_Compile.Result_Success(d_1_v_)

    def UnwrapOr(self, default):
        source1_ = self
        if source1_.is_None:
            return default
        elif True:
            d_2___mcc_h0_ = source1_.value
            d_3_v_ = d_2___mcc_h0_
            return d_3_v_

    def IsFailure(self):
        return (self).is_None

    def PropagateFailure(self):
        return Wrappers_Compile.Option_None()

    def Extract(self):
        return (self).value


class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Option.Some({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Option_Some) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class Result:
    @classmethod
    def default(cls, default_T):
        return lambda: Result_Success(default_T())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Success(self) -> bool:
        return isinstance(self, Wrappers_Compile.Result_Success)
    @property
    def is_Failure(self) -> bool:
        return isinstance(self, Wrappers_Compile.Result_Failure)
    def ToOption(self):
        source2_ = self
        if source2_.is_Success:
            d_4___mcc_h0_ = source2_.value
            d_5_s_ = d_4___mcc_h0_
            return Wrappers_Compile.Option_Some(d_5_s_)
        elif True:
            d_6___mcc_h1_ = source2_.error
            d_7_e_ = d_6___mcc_h1_
            return Wrappers_Compile.Option_None()

    def UnwrapOr(self, default):
        source3_ = self
        if source3_.is_Success:
            d_8___mcc_h0_ = source3_.value
            d_9_s_ = d_8___mcc_h0_
            return d_9_s_
        elif True:
            d_10___mcc_h1_ = source3_.error
            d_11_e_ = d_10___mcc_h1_
            return default

    def IsFailure(self):
        return (self).is_Failure

    def PropagateFailure(self):
        return Wrappers_Compile.Result_Failure((self).error)

    def MapFailure(self, reWrap):
        source4_ = self
        if source4_.is_Success:
            d_12___mcc_h0_ = source4_.value
            d_13_s_ = d_12___mcc_h0_
            return Wrappers_Compile.Result_Success(d_13_s_)
        elif True:
            d_14___mcc_h1_ = source4_.error
            d_15_e_ = d_14___mcc_h1_
            return Wrappers_Compile.Result_Failure(reWrap(d_15_e_))

    def Extract(self):
        return (self).value


class Result_Success(Result, NamedTuple('Success', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Result.Success({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Result_Success) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()

class Result_Failure(Result, NamedTuple('Failure', [('error', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Result.Failure({_dafny.string_of(self.error)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Result_Failure) and self.error == __o.error
    def __hash__(self) -> int:
        return super().__hash__()


class Outcome:
    @classmethod
    def default(cls, ):
        return lambda: Outcome_Pass()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Pass(self) -> bool:
        return isinstance(self, Wrappers_Compile.Outcome_Pass)
    @property
    def is_Fail(self) -> bool:
        return isinstance(self, Wrappers_Compile.Outcome_Fail)
    def IsFailure(self):
        return (self).is_Fail

    def PropagateFailure(self):
        return Wrappers_Compile.Result_Failure((self).error)


class Outcome_Pass(Outcome, NamedTuple('Pass', [])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Outcome.Pass'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Outcome_Pass)
    def __hash__(self) -> int:
        return super().__hash__()

class Outcome_Fail(Outcome, NamedTuple('Fail', [('error', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers_Compile.Outcome.Fail({_dafny.string_of(self.error)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Wrappers_Compile.Outcome_Fail) and self.error == __o.error
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "Wrappers_Compile._default"
    @staticmethod
    def Need(condition, error):
        if condition:
            return Wrappers_Compile.Outcome_Pass()
        elif True:
            return Wrappers_Compile.Outcome_Fail(error)

