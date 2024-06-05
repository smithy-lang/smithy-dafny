package simple.streaming;

import org.reactivestreams.Publisher;
import org.reactivestreams.Subscriber;
import org.reactivestreams.Subscription;
import simple.streaming.model.ChunksInput;
import simple.streaming.model.ChunksOutput;
import simple.streaming.model.CountBitsInput;
import simple.streaming.model.CountBitsOutput;
import simple.streaming.model.SimpleStreamingConfig;
import software.amazon.awssdk.core.async.AsyncRequestBody;
import software.amazon.awssdk.core.async.BlockingOutputStreamAsyncRequestBody;
import software.amazon.awssdk.core.async.SdkPublisher;
import software.amazon.awssdk.utils.BinaryUtils;
import software.amazon.awssdk.utils.async.InputStreamSubscriber;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class SimpleStreamingTest {


    public void inputStream() {
        SimpleStreaming client = SimpleStreaming.builder().build();

        byte[] bits = new byte[] { 1, 2, 3, 4, 5 };
        InputStream bitsIn = new ByteArrayInputStream(bits);
        ExecutorService executorService = Executors.newFixedThreadPool(1);
        Publisher<ByteBuffer> bitsInPublisher = AsyncRequestBody.fromInputStream(bitsIn, 0L, executorService);

        ChunksInput input = ChunksInput.builder()
                .bytesIn(bitsInPublisher)
                .build();
        ChunksOutput output = client.Chunks(input);

        InputStreamSubscriber subscriber = new InputStreamSubscriber();
        output.bytesOut().subscribe(subscriber);
    }

    private static InputStream chunkingInputStream(SimpleStreaming client, InputStream inputBits) {
        ExecutorService executorService = Executors.newFixedThreadPool(1);
        Publisher<ByteBuffer> bitsInPublisher = AsyncRequestBody.fromInputStream(inputBits, 0L, executorService);

        ChunksInput input = ChunksInput.builder()
                .bytesIn(bitsInPublisher)
                .build();
        ChunksOutput output = client.Chunks(input);

        InputStreamSubscriber subscriber = new InputStreamSubscriber();
        output.bytesOut().subscribe(subscriber);
        return subscriber;
    }

    private static OutputStream chunkingOutputStream(SimpleStreaming client, OutputStream outputBits) {
        BlockingOutputStreamAsyncRequestBody bitsInPublisher = AsyncRequestBody.forBlockingOutputStream(0L);

        ChunksInput input = ChunksInput.builder()
                .bytesIn(bitsInPublisher)
                .build();
        ChunksOutput output = client.Chunks(input);

        Subscriber subscriber = new OutputStreamSubscriber(outputBits);
        output.bytesOut().subscribe(subscriber);

        // TODO: This output stream won't pass on any errors
        // recorded
        return bitsInPublisher.outputStream();
    }

    static class OutputStreamSubscriber implements Subscriber<ByteBuffer> {

        private final OutputStream outputStream;
        private Subscription subscription = null;

        OutputStreamSubscriber(OutputStream outputStream) {
            this.outputStream = outputStream;
        }

        @Override
        public void onSubscribe(Subscription s) {
            subscription = s;
        }

        @Override
        public void onNext(ByteBuffer byteBuffer) {
            try {
                outputStream.write(BinaryUtils.copyBytesFrom(byteBuffer));
            } catch (IOException e) {
                // TODO: errors should be recorded
                throw new RuntimeException(e);
            }
        }

        @Override
        public void onError(Throwable t) {
            // TODO: errors should be recorded
        }

        @Override
        public void onComplete() {

        }
    }
}
