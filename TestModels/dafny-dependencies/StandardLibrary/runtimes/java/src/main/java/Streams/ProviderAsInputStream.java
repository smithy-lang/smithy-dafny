package Streams;

import Std_Compile.BulkActions_Compile.BatchArrayWriter;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Consumers_Compile.IgnoreNConsumer;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Wrappers_Compile.Option;
import dafny.Array;
import dafny.TypeDescriptor;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;

public class ProviderAsInputStream extends InputStream {

    private final Producer<Batched<Byte, Exception>> producer;

    public ProviderAsInputStream(Producer<Batched<Byte, Exception>> producer) {
        this.producer = producer;
    }

    @Override
    public int read() throws IOException {
        Option<Batched<Byte, Exception>> next = producer.Next();
        if (next.is_Some()) {
            Batched<Byte, Exception> batched = next.dtor_value();
            if (batched.is_BatchValue()) {
                return next.dtor_value().dtor_value();
            } else if (batched.is_EndOfInput()) {
                return -1;
            } else if (batched.is_BatchError()) {
                throw new IOException(batched.dtor_error());
            } else {
                throw new RuntimeException("Unexpected batched value: " + batched);
            }
        } else {
            return -1;
        }
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        // TODO: Could optimize to use b directly,
        // but that starts to introduce risk.
        Array<Byte> array = Array.newArray(TypeDescriptor.BYTE, len);
        BatchArrayWriter<Byte, Exception> consumer = new BatchArrayWriter<>(
                TypeDescriptor.BYTE, TypeDescriptor.reference(Exception.class)
        );
        consumer.__ctor(array);
        producer.Fill(consumer);
        if (consumer.state.is_Failure()) {
            throw new IOException(consumer.state.dtor_error());
        }
        byte[] results = (byte[])array.unwrap();
        int count = consumer.size.intValueExact();
        if (count == 0) {
            return -1;
        } else {
            System.arraycopy(results, 0, b, off, count);
            return count;
        }
    }

    @Override
    public long skip(long n) throws IOException {
        // TODO: Still need to check for errors and handle EOI
        IgnoreNConsumer<Batched<Byte, Exception>> consumer = new IgnoreNConsumer<>(null);
        consumer.__ctor(BigInteger.valueOf(n));
        producer.Fill(consumer);
        return consumer.consumedCount.longValueExact();
    }
}
