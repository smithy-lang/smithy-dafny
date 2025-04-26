package Streams;

import Std_Compile.BulkActions_Compile.BatchReader;
import Std_Compile.BulkActions_Compile.Batched;
import Std_Compile.Consumers_Compile.IConsumer;
import dafny.Array;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import org.reactivestreams.Subscriber;
import org.reactivestreams.Subscription;

import java.nio.ByteBuffer;
import java.util.concurrent.CompletableFuture;

public class ConsumerAsSubscriber implements Subscriber<ByteBuffer> {

    private final IConsumer<Batched<Byte, Throwable>> consumer
    private final CompletableFuture<Object> future;
    private Subscription subscription;

    private static final TypeDescriptor<Byte> T_TD = TypeDescriptor.BYTE;
    private static final TypeDescriptor<Throwable> E_TD = TypeDescriptor.reference(Throwable.class);
    private static final TypeDescriptor<Batched<Byte, Throwable>> BATCHED_TD =
            Batched._typeDescriptor(T_TD, E_TD);


    public ConsumerAsSubscriber(IConsumer<Batched<Byte, Throwable>> consumer, CompletableFuture<Object> future) {
        this.consumer = consumer;
        this.future = future;
    }

    @Override
    public void onSubscribe(Subscription s) {
        this.subscription = subscription;
        subscription.request(1L);
    }

    @Override
    public void onNext(ByteBuffer o) {
        try {
            byte[] a = new byte[o.remaining()];
            o.get(a);
            Array<Byte> dafnyArray = Array.wrap(a);
            DafnySequence<Byte> dafnySeq = DafnySequence.unsafeWrapArray(dafnyArray);
            BatchReader<Byte, Throwable> reader = new BatchReader(T_TD, E_TD);
            reader.__ctor(dafnySeq);
            reader.ForEach(consumer);

            this.subscription.request(1L);
        } catch (RuntimeException e) {
            this.subscription.cancel();
            this.future.completeExceptionally(e);
        }
    }

    @Override
    public void onError(Throwable t) {
        Batched<Byte, Throwable> event = Batched.create_BatchError(T_TD, E_TD, t);
        consumer.Accept(event);

        this.future.completeExceptionally(t);
    }

    @Override
    public void onComplete() {
        Batched<Byte, Throwable> event = Batched.create_EndOfInput(T_TD, E_TD);
        consumer.Accept(event);

        this.future.complete(null);
    }
}
