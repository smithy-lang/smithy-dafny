# TODO generate this

import simple.types.integer.internaldafny.types
import smithy_generated.simple_integer.client as SimpleInteger
import Wrappers_Compile
import asyncio
from smithy_generated.simple_integer.models import GetIntegerInput

class SimpleIntegerShim(simple.types.integer.internaldafny.types.ISimpleIntegerClient):
    def __init__(self, _impl: SimpleInteger) :
        self._impl = _impl

    def GetInteger(self, input: simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput) -> simple.types.integer.internaldafny.types.GetIntegerOutput_GetIntegerOutput:
        '''
        unwrapped_request = TypeConversion.ToNative(input)
        try:
            wrapped_response = self._impl.get_integer(unwrapped_request)
            return Wrappers_Compile.Result_Success(wrapped_response)
        catch ex:
            return Wrappers_Compile.Result_Failure(ex)
        '''

        unwrapped_request: GetIntegerInput = GetIntegerInput(value=input.value)
        wrapped_response = asyncio.run(self._impl.get_integer(unwrapped_request))
        return Wrappers_Compile.Result_Success(wrapped_response)
        
        
        