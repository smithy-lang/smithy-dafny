
from _dafny import Seq
from smithy_python.interfaces.blobs import ByteStream
from smithy_dafny_standard_library.internaldafny.generated.Std_Streams import ByteStream as DafnyByteStream, RewindableByteStream as DafnyRewindableByteStream
from smithy_dafny_standard_library.internaldafny.generated.Std_Enumerators import Enumerator
from smithy_dafny_standard_library.internaldafny.generated.Std_Wrappers import Option, Option_Some, Option_None

# Adaptor classes for wrapping up Python-native types as their
# corresponding Dafny interfaces, and vice-versa.
# These are the equivalent of type conversions,
# but avoiding having to load all data into memory at once.

class DafnyByteStreamAsByteStream(ByteStream):
  """Wrapper class adapting a Dafny ByteStream as a native ByteStream."""

  def __init__(self, dafny_byte_stream):
    self.dafny_byte_stream = dafny_byte_stream

  def read(self, size: int = -1) -> bytes:
    # TODO: assert size is -1, buffer, 
    # or define a more specialized Action<int, bytes> type for streams.
    next = self.dafny_byte_stream.Next()
    while next.is_Some and len(next.value) == 0:
      next = self.dafny_byte_stream.Next()
    # Do NOT return None, because that indicates "no data right now, might be more later"
    return bytes(next.value) if next.is_Some else bytes()


class RewindableDafnyByteStreamAsByteStream(DafnyByteStreamAsByteStream):
  """Wrapper class adapting a Dafny RewindableByteStream as a native ByteStream
  that supports tell and seek.
  """

  def __init__(self, dafny_byte_stream):
    if not isinstance(dafny_byte_stream, DafnyRewindableByteStream):
      raise ValueError("Rewindable stream required")
    super().__init__(dafny_byte_stream)

  def tell(self) -> int:
    return self.dafny_byte_stream.Position()

  def seek(self, offset, whence=0):
    match whence:
      case 0:
        position = offset
      case 1:
        position = self.dafny_byte_stream.Position() + offset
      case 2:
        position = self.dafny_byte_stream.ContentLength() + offset
    return self.dafny_byte_stream.Seek(position)


class StreamingBlobAsDafnyDataStream(DafnyByteStream):
  """Wrapper class adapting a native StreamingBlob as a Dafny ByteStream."""

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
