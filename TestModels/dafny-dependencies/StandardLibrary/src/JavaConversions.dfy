include "Actions.dfy"
include "UInt.dfy"

module StandardLibraryJavaConversions {

  import opened StandardLibrary.UInt
  import opened StandardLibrary.Actions
  import opened Wrappers

  class {:compile false} {:extern "java.lang.Void"} Void {

  }

  trait {:compile false} {:extern "java.util.function.Consumer"} Consumer<T> {

    method {:extern} accept(t: T)
  }
  
  trait {:compile false} {:extern "java.lang.Throwable"} Throwable {

  }

  trait {:compile false} {:compile false} {:extern "java.util.concurrent.CompletableFuture"} CompletableFuture<T> {

  }

  trait {:compile false} {:extern "org.reactivestreams.Subscription"} Subscription {

    method {:extern} request(n: int64)

    method {:extern} cancel()
  }

  trait {:compile false} {:extern "software.amazon.awssdk.core.asyn.SdkPublisher"} SdkPublisher<T> {

    method {:extern} subscribe(s: Subscriber<T>) returns (f: Subscription)

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

  class SequentialSubscriber<T> extends Subscriber<T> {

    var subscription: Subscription?
    var action: Action<StreamEvent<T, Throwable>, ()>

    constructor(a: Action<StreamEvent<T, Throwable>, ()>) {
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

  method AsSequentialSubscriber<T>(a: Action<StreamEvent<T, Throwable>, ()>) returns (s: Subscriber<T>) {
    s := new SequentialSubscriber(a);
  }

  // TODO: Rich specification to fill out here.
  // This could be useful for analysize existing Java codebases to see
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