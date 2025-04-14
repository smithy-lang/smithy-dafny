
from _dafny import Seq
from smithy_python.interfaces.blobs import ByteStream
from smithy_dafny_standard_library.internaldafny.generated.Std_Streams import DataStream as DafnyDataStream, RewindableDataStream as DafnyRewindableDataStream
from smithy_dafny_standard_library.internaldafny.generated.Std_Enumerators import Enumerator
from smithy_dafny_standard_library.internaldafny.generated.Std_Wrappers import Option, Option_Some, Option_None

# Adaptor classes for wrapping up Python-native types as their
# corresponding Dafny interfaces, and vice-versa.
# These are the equivalent of type conversions,
# but avoiding having to load all data into memory at once.

class DafnyDataStreamAsByteStream(ByteStream):
  """Wrapper class adapting a Dafny DataStream as a native ByteStream."""

  def __init__(self, dafny_data_stream):
    self.dafny_data_stream = dafny_data_stream

  def read(self, size: int = -1) -> bytes:
    next = None
    while next is None or (next.is_Some and len(next.value) == 0):
      if size == -1:
        next = self.dafny_data_stream.Next()
      else:
        next = self.dafny_byte_stream.Read(size)

    # Do NOT return None, because that indicates "no data right now, might be more later"
    return bytes(next.value) if next.is_Some else bytes()


class DafnyRewindableDataStreamAsByteStream(DafnyByteStreamAsByteStream):
  """Wrapper class adapting a Dafny RewindableDataStream as a native ByteStream
  that supports tell and seek.
  """

  def __init__(self, dafny_data_stream):
    if not isinstance(dafny_data_stream, DafnyRewindableDataStream):
      raise ValueError("Rewindable stream required")
    super().__init__(dafny_data_stream)

  def tell(self) -> int:
    return self.dafny_data_stream.Position()

  def seek(self, offset, whence=0):
    match whence:
      case 0:
        position = offset
      case 1:
        position = self.dafny_data_stream.Position() + offset
      case 2:
        position = self.dafny_data_stream.totalLength.value + offset
    return self.dafny_data_stream.Seek(position)


class StreamingBlobAsDafnyDataStream(DafnyDataStream):
  """Wrapper class adapting a native StreamingBlob as a Dafny ByteStream."""

  def __init__(self, streaming_blob):
    self.streaming_blob = streaming_blob

  def Next(self):
    return Producer.Next(self)

  def Invoke(self, _) -> Option:
    next = self.streaming_blob.read()
    if next:
      return Option_Some(Seq(next))
    else:
      return Option_None()

  def Read(self, size) -> Option:
    next = self.streaming_blob.read(size)
    if next:
      return Option_Some(Seq(next))
    else:
      return Option_None()
