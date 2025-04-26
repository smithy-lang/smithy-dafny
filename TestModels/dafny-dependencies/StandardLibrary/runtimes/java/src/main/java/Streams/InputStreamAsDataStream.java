package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Wrappers_Compile.Option;

import java.io.InputStream;
import java.math.BigInteger;

public class InputStreamAsDataStream implements DataStream<Exception> {

    private final InputStream inputStream;
    private boolean read = false;

    public InputStreamAsDataStream(InputStream inputStream) {
        this.inputStream = inputStream;
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
    public Producer<Batched<Byte, Exception>> Reader() {
        if (read) {
            throw new IllegalStateException("Already read");
        }
        read = true;

        return new InputStreamAsProducer(inputStream);
    }
}
