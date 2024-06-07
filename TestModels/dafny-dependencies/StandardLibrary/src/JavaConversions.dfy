include "Actions.dfy"
include "UInt.dfy"

module StandardLibraryJavaConversions {

  import opened StandardLibrary.UInt
  import opened StandardLibrary.Actions
  import opened Wrappers
  
  trait {:compile false} {:extern "java.lang.Throwable"} Throwable {

  }

  trait {:compile false} {:extern "java.util.concurrent.CompletableFuture"} CompletableFuture<T> {

  }

  trait {:compile false} {:extern "org.reactivestreams.Subscription"} Subscription {

    method request(n: int64)

    method cancel()
  }

  trait {:compile false} {:extern "org.reactivestreams.Publisher"} Publisher<T> {

    method subscribe(s: Subscriber<T>)

  }

  trait {:compile false} {:extern "org.reactivestreams.Subscriber"} Subscriber<T> {

    // NOTE: Don't put {:extern} on these,
    // or else no code will be emitted for the implementations.

    method onSubscribe(s: Subscription)
      modifies this

    method onNext(t: T)

    method onError(t: Throwable)

    method onComplete()
  }

  // Publisher<T> -> Action

  class SequentialActionSubscriber<T> extends Subscriber<T> {

    var subscription: Subscription?
    var action: Action<Result<T, Throwable>, ()>

    constructor(a: Action<Result<T, Throwable>, ()>) {
      this.action := a;
    }

    method onSubscribe(s: Subscription) 
      modifies this
    {
      this.subscription := s;
      subscription.request(1);
    }

    method {:verify false} onNext(t: T) {
      var _ := action.Call(Some(Success(t)));
      subscription.request(1);
    }

    method {:verify false} onError(t: Throwable) {
      var _ := action.Call(Some(Failure(t)));
    }

    method {:verify false} onComplete() {
      var _ := action.Call(None);
    }

  }

  method AsSequentialSubscriber<T>(a: Action<Result<T, Throwable>, ()>) returns (s: Subscriber<T>) {
    s := new SequentialActionSubscriber(a);
  }

  class SubscribingAction<T> extends Stream<Result<T, Throwable>> {

    const publisher: Publisher<T>    

    constructor(publisher: Publisher<T>) {
      this.publisher := publisher;
    }
    
    method Next() returns (r: Option<Result<T, Throwable>>) {
      // TODO: Connect to PublisherInputStream
      r := None;
    }

    method ForEach(a: Accumulator<Result<T, Throwable>>) {
      var subscriber := AsSequentialSubscriber(a);
      publisher.subscribe(subscriber);

      // TODO: Needs to wait on completion (needs an extern)
    }
  }

  method AsStream<T>(p: Publisher<T>) returns (s: Stream<StreamEvent<T, Throwable>>) {
    s := new SubscribingAction(p);
  } 

  // Stream -> Pulisher<T>

  class SubscriberAction<T> extends Action<StreamEvent<T, Throwable>, ()> {

    const subscriber: Subscriber<T>

    constructor(subscriber: Subscriber<T>) {
      this.subscriber := subscriber;
    }

    // TODO: Need built in buffering so the subscriber isn't actually
    // called unless the subscription requests values.
    // OR expose an isomorphic concept and thread it through.
    method Call(e: StreamEvent<T, Throwable>) returns (nothing: ()) {
      match e {
        case Some(Success(value)) => {
          subscriber.onNext(value);
        }
        case Some(Failure(throwable)) => {
          subscriber.onError(throwable);
        }
        case None => {
          subscriber.onComplete();
        }
      }
      return ();
    }

  }

  class ActionPublisher<T> extends Publisher<T> {
    const subscribeAction: Stream<StreamEvent<T, Throwable>>

    constructor(subscribeAction: Stream<StreamEvent<T, Throwable>>) {
      this.subscribeAction := subscribeAction;
    }

    method {:verify false} subscribe(s: Subscriber<T>) {
      var action := new SubscriberAction(s);
      subscribeAction.ForEach(action);
    }
  }

  method AsPublisher<T>(a: Stream<StreamEvent<T, Throwable>>) returns (s: Publisher<T>) {
    s := new ActionPublisher(a);
  } 

  // ByteBuffers

  // TODO: Rich specification to fill out here.
  // This could be useful for analyzing existing Java codebases to see
  // if they use ByteBuffers correctly!
  trait {:compile false} {:extern "java.nio.ByteBuffer"} ByteBuffer {
    function method {:extern} remaining(): int32
      ensures remaining() >= 0
    function method {:extern} position(): int32
      ensures position() as int + remaining() as int < INT32_MAX_LIMIT
    function method {:extern} get(i: int32): uint8
    method {:extern} put(b: uint8)

    static method allocate(capacity: int32) returns (bb: ByteBuffer)
  }

  method AsBytesRemaining(bb: ByteBuffer) returns (res: seq<uint8>) {
    // TODO: This is about as efficient as we can get in Dafny code,
    // but this is a reasonable case to implement in the Java runtime better instead.
    var length := bb.remaining();
    var start := bb.position();
    res := seq(length, (i: nat) requires 0 <= i < length as nat => bb.get(i as int32 + start));
  }


  method ToByteBuffer(b: seq<uint8>) returns (res: ByteBuffer) 
    requires |b| < INT32_MAX_LIMIT
  {
    // TODO: Could do better with native arrays etc.
    // but this is a reasonable case to implement in the Java runtime better instead.
    var length := |b| as int32;
    res := ByteBuffer.allocate(length);
    for i := 0 to length {
      res.put(b[i]);
    }
  }

}