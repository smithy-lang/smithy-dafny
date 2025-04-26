package Streams;

import StandardLibrary_Compile.Streams_Compile.DataStream;
import software.amazon.awssdk.http.ContentStreamProvider;

import java.io.InputStream;

public class DataStreamAsContentStreamProvider implements ContentStreamProvider {

    private final DataStream dataStream;

    public DataStreamAsContentStreamProvider(DataStream dataStream) {
        this.dataStream = dataStream;
    }

    @Override
    public InputStream newStream() {
        return new ProviderAsInputStream(dataStream.Reader());
    }
}
