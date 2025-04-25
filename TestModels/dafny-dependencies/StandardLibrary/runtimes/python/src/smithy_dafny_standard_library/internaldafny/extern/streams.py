
from _dafny import Seq
from smithy_python.interfaces.blobs import ByteStream
from smithy_dafny_standard_library.internaldafny.generated.StandardLibrary_Streams import DataStream
from smithy_dafny_standard_library.internaldafny.generated.Std_BulkActions import BatchSeqWriter, BatchArrayWriter
from smithy_dafny_standard_library.internaldafny.generated.Std_Wrappers import Option, Option_Some, Option_None

# Adaptor classes for wrapping up Python-native types as their
# corresponding Dafny interfaces, and vice-versa.
# These are the equivalent of type conversions,
# but avoiding having to load all data into memory at once.

class DafnyDataStreamAsByteStream(ByteStream):
  """Wrapper class adapting a Dafny DataStream as a native ByteStream."""

  def __init__(self, data_stream):
    self.data_stream = data_stream
    self.reader = data_stream.Reader()

  def read(self, size: int = -1) -> bytes:
    if size == -1:
      writer = new BatchSeqWriter()
      self.reader.ForEach(writer)
    else:
      writer = new BatchArrayWriter(size)
      self.reader.ForEachToCapacity(writer)
    # TODO: Check for errors. Fine to ignore EOI though.
    return bytes(writer.elements)

  def tell(self) -> int:
    return self.reader.ProducedCount()

  def seek(self, offset, whence=0):
    # TODO: check whether invalid offsets must raise errors
    match whence:
      case 0:
        new_position = offset
      case 1:
        new_position = self.reader.Position() + offset
      case 2:
        new_position = self.data_stream.ContentLength().value + offset

    if position > self.reader.Position():
      self.reader.ForEach(new IgnoreNConsumer(position - self.reader.Position()))
    else if position < self.reader.Position():
      self.reader = data_stream.Reader()
      self.reader.ForEach(new IgnoreNConsumer(position))


class StreamingBlobAsDafnyDataStream(DafnyDataStream):
  """Wrapper class adapting a native StreamingBlob as a Dafny DataStream."""

  def __init__(self, streaming_blob):
    self.streaming_blob = streaming_blob

  def Next(self):
    return Producer.Next(self)

  def Invoke(self, _) -> Option:
    # TODO: error handling
    next = self.streaming_blob.read(1)
    if next:
      return Option_Some(Option_Some(Result_Success(next)))
    else:
      return Option_None()

  def ProducedCount(self):
    return self.streaming_blob.position

  def ForEach(self, consumer):
    # TODO: error handling
    while next = self.streaming_blob.read(4096):
      batch = new BatchReader(Seq(next))
      batch.ForEach(consumer)
    batch.Accept(Option_None)

  def ForEachToCapacity(self, consumer):
    # TODO: error handling
    size = consumer.Capacity()
    next = self.streaming_blob.read(size)
    batch = new BatchReader(Seq(next))
    batch.ForEachToCapacity(consumer)
