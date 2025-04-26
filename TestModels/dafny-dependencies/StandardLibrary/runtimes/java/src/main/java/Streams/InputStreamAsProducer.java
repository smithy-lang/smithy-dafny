package Streams;

import Std_Compile.BulkActions_Compile.BatchArrayWriter;
import Std_Compile.BulkActions_Compile.BatchReader;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Consumers_Compile.Consumer;
import Std_Compile.Consumers_Compile.IConsumer;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Producers_Compile._Companion_Producer;
import Std_Compile.Producers_Compile.__default;
import Std_Compile.Wrappers_Compile.Option;
import dafny.Array;
import dafny.DafnySequence;
import dafny.Tuple0;
import dafny.TypeDescriptor;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;

public class InputStreamAsProducer implements Producer<Batched<Byte, Exception>> {

    private final InputStream inputStream;
    private long totalRead;

    private static final TypeDescriptor<Byte> T_TD = TypeDescriptor.BYTE;
    private static final TypeDescriptor<Exception> E_TD = TypeDescriptor.reference(Exception.class);
    private static final TypeDescriptor<Batched<Byte, Exception>> BATCHED_TD =
            Batched._typeDescriptor(T_TD, E_TD);

    public InputStreamAsProducer(InputStream inputStream) {
        this.inputStream = inputStream;
        this.totalRead = 0;
    }

    @Override
    public BigInteger ProducedCount() {
        return BigInteger.valueOf(totalRead);
    }

    @Override
    public Option<BigInteger> Remaining() {
        return Option.create_None(TypeDescriptor.BIG_INTEGER);
    }

    @Override
    public Option<Batched<Byte, Exception>> Next() {
        try {
            int value = inputStream.read();
            if (value == -1) {
                // TODO: EOI
                return Option.create_None(BATCHED_TD);
            } else {
                Batched batched = Batched.create_BatchValue(T_TD, E_TD, (byte)value);
                return Option.create_Some(BATCHED_TD, batched);
            }
        } catch (IOException e) {
            return Option.create_Some(null, Batched.create_BatchError(T_TD, E_TD, e));
        }
    }

    @Override
    public void ForEach(IConsumer<Batched<Byte, Exception>> consumer) {
        __default.DefaultForEach(BATCHED_TD, this, consumer);
    }

    @Override
    public Option<Batched<Byte, Exception>> Fill(Consumer<Batched<Byte, Exception>> consumer) {
        if (consumer instanceof BatchArrayWriter) {
            BatchArrayWriter<Byte, Exception> writer = (BatchArrayWriter) consumer;
            int n = writer.Capacity().dtor_value().intValueExact();
            byte[] buffer = new byte[n];
            try {
                int count = inputStream.read(buffer, 0, n);
                if (count == -1) {
                    consumer.Accept(Batched.create_EndOfInput(T_TD, E_TD));
                } else {
                    totalRead += count;
                    Array<Byte> dafnyArray = Array.wrap(buffer);
                    BatchReader<Byte, Exception> reader = new BatchReader(T_TD, E_TD);
                    reader.__ctor(DafnySequence.fromArrayRange(T_TD, dafnyArray, 0, count));
                    reader.Fill(consumer);
                }
            } catch (IOException e) {
                writer.Accept(Batched.create_BatchError(T_TD, E_TD, e));
            }
            return Option.create_None(BATCHED_TD);
        }

        return __default.DefaultFill(BATCHED_TD, this, consumer);
    }

    @Override
    public Option<Batched<Byte, Exception>> Invoke(Tuple0 tuple0) {
        return _Companion_Producer.Next(null, this);
    }
}
