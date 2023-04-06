# TODO generate this

import Dafny.Simpletypes.Boolean.Types
import simple_boolean.client as SimpleBoolean
import Wrappers_Compile
import asyncio
from simple_boolean.models import GetBooleanInput

class SimpleBooleanShim(Dafny.Simpletypes.Boolean.Types.ISimpleBooleanClient):
    def __init__(self, _impl: SimpleBoolean) :
        self._impl = _impl

    def GetBoolean(self, input: Dafny.Simpletypes.Boolean.Types.GetBooleanInput_GetBooleanInput) -> Dafny.Simpletypes.Boolean.Types.GetBooleanOutput_GetBooleanOutput:
        '''
        unwrapped_request = TypeConversion.ToNative(input)
        try:
            wrapped_response = self._impl.get_boolean(unwrapped_request)
            return Wrappers_Compile.Result_Success(wrapped_response)
        catch ex:
            return Wrappers_Compile.Result_Failure(ex)
        '''

        print(f"this is input.value {input.value}")
        unwrapped_request: GetBooleanInput = GetBooleanInput(value=input.value)
        print(f"this is unwrapped_request {unwrapped_request}")
        wrapped_response = asyncio.run(self._impl.get_boolean(unwrapped_request))
        print(f"this is wrapped_response {wrapped_response}")
        return Wrappers_Compile.Result_Success(wrapped_response)
        
        
        