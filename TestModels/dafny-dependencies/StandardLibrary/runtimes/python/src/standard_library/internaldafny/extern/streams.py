
from _dafny import Seq
from smithy_python.interfaces.blobs import ByteStream
from standard_library.internaldafny.generated.Std_Enumerators import Enumerator
from standard_library.internaldafny.generated.Wrappers import Option, Option_Some, Option_None


class EnumeratorByteStream(ByteStream):
  
  def __init__(self, dafny_enumerator):
    self.dafny_enumerator = dafny_enumerator

  def read(self, size: int = -1) -> bytes:
    # TODO: assert size is -1, buffer, 
    # or define a more specialized Action<int, bytes> type for streams.
    next = Enumerator.Next(self.dafny_enumerator)
    while next.is_Some and len(next.value) == 0:
      next = Enumerator.Next(self.dafny_enumerator)
    # Do NOT return None, because that indicates "no data right now, might be more later"
    return bytes(next.value) if next.is_Some else bytes() 


class StreamingBlobEnumerator(Enumerator):
  
  def __init__(self, streaming_blob):
    self.streaming_blob = streaming_blob

  def Next(self):
    return Enumerator.Next(self)

  def Invoke(self, _) -> Option:
    next = self.streaming_blob.read()
    if next:
      return Option_Some(Seq(next))
    else:
      return Option_None()
    
