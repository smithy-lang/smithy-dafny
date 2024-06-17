include "UInt.dfy"
include "StandardLibrary.dfy"
include "Actions.dfy"

module {:options "--function-syntax:4"} StandardLibraryJavaConversions {

  import opened StandardLibrary.UInt
  import opened Std.Actions
  import opened Wrappers
  
  // TODO: Add these aliases to the main Actions library?
  type Action'<T(!new), R(!new)> = Action<T, T, R, R>
  type Enumerator'<T(!new)> = Enumerator<T, T>
  type Accumulator'<T(!new)> = Accumulator<T, T>
  type Stream'<T(!new)> = Stream<T, T>

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

  type SubscriptionEvent<T(!new)> = Option<Result<T, Throwable>>

  // Publisher<T> -> Action

  class SequentialActionSubscriber<T(!new)> extends Subscriber<T> {

    var subscription: Subscription?
    var action: Action'<SubscriptionEvent<T>, ()>

    constructor(a: Action'<SubscriptionEvent<T>, ()>) {
      this.action := a;
    }

    method onSubscribe(s: Subscription) 
      modifies this
    {
      this.subscription := s;
      subscription.request(1);
    }

    method {:verify false} onNext(t: T) {
      var _ := action.Invoke(Some(Success(t)));
      subscription.request(1);
    }

    method {:verify false} onError(t: Throwable) {
      var _ := action.Invoke(Some(Failure(t)));
    }

    method {:verify false} onComplete() {
      var _ := action.Invoke(None);
    }

  }

  method AsSequentialSubscriber<T>(a: Action'<SubscriptionEvent<T>, ()>) returns (s: Subscriber<T>) {
    s := new SequentialActionSubscriber(a);
  }

  class SubscribingAction<T> extends Action<(), (), SubscriptionEvent<T>, SubscriptionEvent<T>> {

    const publisher: Publisher<T>

    constructor(publisher: Publisher<T>) {
      this.publisher := publisher;
    }
    
    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr
    }
    
    ghost predicate CanConsume(history: seq<((), SubscriptionEvent<T>)>, next: ())
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<((), SubscriptionEvent<T>)>)
      decreases height
    {
      true
    }

    method Invoke(nothing: ()) returns (r: SubscriptionEvent<T>) {
      // TODO: Connect to PublisherInputStream
      r := None;
    }

    method ForEach(a: Accumulator'<Result<T, Throwable>>) {
      var subscriber := AsSequentialSubscriber(a);
      publisher.subscribe(subscriber);

      // TODO: Needs to wait on completion (needs an extern)
    }
  }

  method AsStream<T>(p: Publisher<T>) returns (s: Enumerator'<Result<T, Throwable>>) {
    s := new SubscribingAction(p);
  } 

  // Stream -> Pulisher<T>

  class SubscriberAction<T> extends Action<SubscriptionEvent<T>, SubscriptionEvent<T>, (), ()> {

    const subscriber: Subscriber<T>

    constructor(subscriber: Subscriber<T>) {
      this.subscriber := subscriber;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr
    }
    
    ghost predicate CanConsume(history: seq<(SubscriptionEvent<T>, ())>, next: SubscriptionEvent<T>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(SubscriptionEvent<T>, ())>)
      decreases height
    {
      true
    }

    method Invoke(e: SubscriptionEvent<T>) returns (nothing: ()) {
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
    const subscribeAction: Stream'<Result<T, Throwable>>

    constructor(subscribeAction: Enumerator'<Result<T, Throwable>>) {
      this.subscribeAction := subscribeAction;
    }

    method {:verify false} subscribe(s: Subscriber<T>) {
      var action := new SubscriberAction(s);
      subscribeAction.ForEach(action);
    }
  }

  method AsPublisher<T>(a: Enumerator'<Result<T, Throwable>>) returns (s: Publisher<T>) {
    s := new ActionPublisher(a);
  } 

  // ByteBuffers

  // TODO: Rich specification to fill out here.
  // This could be useful for analyzing existing Java codebases to see
  // if they use ByteBuffers correctly!
  trait {:compile false} {:extern "java.nio.ByteBuffer"} ByteBuffer {
    function {:extern} remaining(): int32
      ensures remaining() >= 0
    function {:extern} position(): int32
      ensures position() as int + remaining() as int < INT32_MAX_LIMIT
    function {:extern} get(i: int32): uint8
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