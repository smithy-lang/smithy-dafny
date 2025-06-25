package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Wrappers_Compile.Option;
import dafny.TypeDescriptor;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.util.function.Function;

public class InputStreamAsDataStream<E> implements DataStream<Byte, E> {

    private final TypeDescriptor<E> e_td;

    private final InputStream inputStream;
    private final Function<IOException, E> ioExceptionWrapper;
    private boolean read = false;

    public InputStreamAsDataStream(TypeDescriptor<E> e_td, InputStream inputStream, Function<IOException, E> ioExceptionWrapper) {
        this.e_td = e_td;
        this.inputStream = inputStream;
        this.ioExceptionWrapper = ioExceptionWrapper;
    }

    @Override
    public Option<BigInteger> ContentLength() {
        return Option.create_None(null);
    }

    @Override
    public boolean Replayable() {
        return false;
    }

    @Override
    public Producer<Batched<Byte, E>> Reader() {
        if (read) {
            throw new IllegalStateException("Already read");
        }
        read = true;

        return new InputStreamAsProducer(e_td, inputStream, ioExceptionWrapper);
    }
}
