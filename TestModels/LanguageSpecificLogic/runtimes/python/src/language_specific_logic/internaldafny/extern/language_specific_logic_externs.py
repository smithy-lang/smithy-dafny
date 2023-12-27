import PythonLanguageSpecificLogicImpl
import sys
import Wrappers
import _dafny

class default__(PythonLanguageSpecificLogicImpl.default__):
    @staticmethod
    def GetPythonRuntimeVersion(config):
        return Wrappers.Result_Success(_dafny.Seq(str(sys.version)))

PythonLanguageSpecificLogicImpl.default__ = default__