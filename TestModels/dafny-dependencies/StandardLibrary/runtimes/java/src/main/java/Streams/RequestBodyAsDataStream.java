package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Wrappers_Compile.Option;
import dafny.TypeDescriptor;
import software.amazon.awssdk.core.sync.RequestBody;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.util.Optional;
import java.util.function.Function;

public class RequestBodyAsDataStream<E>  implements DataStream<Byte, E> {

    private final TypeDescriptor<E> e_td;
    private final Function<IOException, E> ioExceptionWrapper;
    private final RequestBody requestBody;

    public RequestBodyAsDataStream(TypeDescriptor<E> e_td, RequestBody requestBody, Function<IOException, E> ioExceptionWrapper) {
        this.e_td = e_td;
        this.ioExceptionWrapper = ioExceptionWrapper;
        this.requestBody = requestBody;
    }

    @Override
    public Option<BigInteger> ContentLength() {
        if (requestBody.optionalContentLength().isPresent()) {
            return Option.create_Some(TypeDescriptor.BIG_INTEGER, BigInteger.valueOf(requestBody.optionalContentLength().get()));
        } else {
            return Option.create_None(TypeDescriptor.BIG_INTEGER);
        }
    }

    @Override
    public boolean Replayable() {
        return true;
    }

    @Override
    public Producer<Batched<Byte, E>> Reader() {
        InputStream is = requestBody.contentStreamProvider().newStream();
        return new InputStreamAsProducer<>(e_td, is, ioExceptionWrapper);
    }
}
