package Streams;

import org.reactivestreams.Publisher;
import org.reactivestreams.Subscriber;
import org.reactivestreams.Subscription;

import java.io.IOException;
import java.io.InputStream;
import java.nio.ByteBuffer;

public class PublisherInputStream extends InputStream implements Subscriber<ByteBuffer> {

    // TODO: Generalize to an Iterator<T> ?

    private Subscription subscription;
    private ByteBuffer current;
    private Throwable error;
    private boolean complete;


    public PublisherInputStream() {
    }

    @Override
    public int read() throws IOException {
        throw new UnsupportedOperationException();
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        // TODO: Error if never subscribed
        if (current == null) {
            if (complete) {
                return 0;
            }

            // TODO: wait on semaphore
        }

        if (error != null) {
            throw new IOException(error);
        } else if (complete) {
            return 0;
        }

        int toGet = Math.min(len, current.remaining());
        current.get(b, off, toGet);
        if (current.remaining() == 0) {
            current = null;
            // TODO: Could make request configurable.
            subscription.request(1);
        }

        return toGet;
    }

    @Override
    public void onSubscribe(Subscription s) {
        subscription = subscription;
        subscription.request(1);
    }

    @Override
    public void onNext(ByteBuffer byteBuffer) {
        if (byteBuffer.remaining() > 0) {
            current = byteBuffer;
            // TODO: semaphore
        }
    }

    @Override
    public void onError(Throwable t) {
        error = t;
        // TODO: semaphore
    }

    @Override
    public void onComplete() {
        complete = true;
        // TODO: semaphore
    }
}
