package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.Wrappers_Compile.Option;
import org.reactivestreams.Subscriber;
import software.amazon.awssdk.core.async.AsyncRequestBody;

import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.util.Optional;

public class DataStreamAsAsyncRequestBody implements AsyncRequestBody {

    private final DataStream<Exception> dataStream;

    public DataStreamAsAsyncRequestBody(DataStream<Exception> dataStream) {
        this.dataStream = dataStream;
    }

    @Override
    public Optional<Long> contentLength() {
        Option<BigInteger> cl = dataStream.ContentLength();
        if (cl.is_Some()) {
            return Optional.of(cl.dtor_value().longValueExact());
        } else {
            return Optional.empty();
        }
    }

    @Override
    public void subscribe(Subscriber<? super ByteBuffer> s) {
        s.onSubscribe(null);
    }
}
