
from _dafny import Seq, Array as DafnyArray
from smithy_python.interfaces.blobs import ByteStream
from smithy_dafny_standard_library.internaldafny.generated.StandardLibrary_Streams import DataStream
from smithy_dafny_standard_library.internaldafny.generated.Std_BulkActions import BatchSeqWriter, BatchArrayWriter, Batched_BatchValue, Batched_EndOfInput, BatchReader
from smithy_dafny_standard_library.internaldafny.generated.Std_Consumers import IgnoreNConsumer
from smithy_dafny_standard_library.internaldafny.generated.Std_Producers import Producer
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
      writer = BatchSeqWriter()
      writer.ctor__()
      self.reader.ForEach(writer)
    else:
      writer = BatchArrayWriter()
      writer.ctor__(DafnyArray(None, size))
      self.reader.Fill(writer)

    # TODO: Check for errors. Fine to ignore EOI though.
    return bytes(writer.Values())

  def tell(self) -> int:
    return self.reader.ProducedCount()

  def seek(self, offset, whence=0):
    # TODO: check whether invalid offsets must raise errors
    # TODO: Need to -1 to account for EndOfInput
    match whence:
      case 0:
        new_position = offset
      case 1:
        new_position = self.reader.ProducedCount() + offset
      case 2:
        new_position = self.data_stream.ContentLength().value + offset

    if new_position > self.reader.ProducedCount():
      consumer = IgnoreNConsumer()
      consumer.ctor__(new_position - self.reader.ProducedCount())
      self.reader.Fill(consumer)
    elif new_position < self.reader.ProducedCount():
      self.reader = self.data_stream.Reader()
      consumer = IgnoreNConsumer()
      consumer.ctor__(new_position)
      self.reader.Fill(consumer)
      

class StreamingBlobAsDafnyDataStream(DataStream):
  def __init__(self, streaming_blob):
    self.streaming_blob = streaming_blob
    self.read = False

  def Replayable(self):
    False

  def Reader(self):
    if self.read:
      raise Exception("StreamingBlobAsDafnyDataStream.Reader() called twice")
    self.read = True
    return StreamingBlobAsDafnyProducer(self.streaming_blob)


# TODO: Missing some methods like Remaining()
class StreamingBlobAsDafnyProducer(Producer):
  """Wrapper class adapting a native StreamingBlob as a Dafny DataStream."""

  def __init__(self, streaming_blob):
    self.streaming_blob = streaming_blob
    self.emitted_eoi = False

  def Next(self):
    return Producer.Next(self)

  def Invoke(self, _) -> Option:
    if self.emitted_eoi:
      return Option_None()
    
    # TODO: error handling
    next = self.streaming_blob.read(1)
    if next:
      return Option_Some(Batched_BatchValue(next[0]))
    else:
      self.emitted_eoi = True
      return Option_Some(Batched_EndOfInput())

  def ProducedCount(self):
    return self.streaming_blob.position

  def ForEach(self, consumer):
    if self.emitted_eoi:
      return

    # TODO: error handling
    while True:
      next = self.streaming_blob.read(4096)
      if not next:
        break
      batch = BatchReader()
      batch.ctor__(Seq(next))
      batch.ForEach(consumer)
  
    consumer.Accept(Batched_EndOfInput())
    self.emitted_eoi = True

  def Fill(self, consumer):
    if self.emitted_eoi:
      return

    # TODO: error handling
    size = consumer.Capacity()
    next = self.streaming_blob.read(size)
    if not next:
      self.emitted_eoi = True
      eoi = Batched_EndOfInput()
      consumer.Accept(eoi)
    else:
      batch = BatchReader()
      batch.ctor__(Seq(next))
      batch.Fill(consumer)
