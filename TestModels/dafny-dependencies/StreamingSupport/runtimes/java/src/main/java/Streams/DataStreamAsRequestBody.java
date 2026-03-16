package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import Std_Compile.Producers_Compile.Producer;
import Std_Compile.Wrappers_Compile.Option;
import software.amazon.awssdk.core.sync.RequestBody;
import software.amazon.awssdk.http.ContentStreamProvider;

import java.math.BigInteger;

public class DataStreamAsRequestBody {

    public static <E> RequestBody of(DataStream<Byte, E> dataStream) {
        final ContentStreamProvider provider = () -> {
            Producer reader = dataStream.Reader();
            return new ProducerAsInputStream(reader);
        };
        final Option<BigInteger> contentLength = dataStream.ContentLength();

        return contentLength.is_Some()
            ? RequestBody.fromContentProvider(provider, contentLength.dtor_value().longValueExact(), "application/octet-stream")
            : RequestBody.fromContentProvider(provider, "application/octet-stream");
    }
}
