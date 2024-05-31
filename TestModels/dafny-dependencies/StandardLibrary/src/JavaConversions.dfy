include "Actions.dfy"
include "UInt.dfy"

module StandardLibraryJavaConversions {

  import opened StandardLibrary.UInt
  import opened StandardLibrary.Actions
  import opened Wrappers

  class {:extern "java.lang.Void"} Void {

  }

  trait {:extern "java.util.function.Consumer"} Consumer<T> {

    method {:extern} accept(t: T)
  }
  
  trait {:extern "java.lang.Throwable"} Throwable {

  }

  trait {:extern "java.util.concurrent.CompletableFuture"} CompletableFuture<T> {

  }

  trait {:extern "org.reactivestreams.Subscription"} Subscription {

    method {:extern} request(n: int64)

    method {:extern} cancel()
  }

  trait {:extern "software.amazon.awssdk.core.asyn.SdkPublisher"} SdkPublisher<T> {

    method {:extern} subscribe(s: Subscriber<T>) returns (f: Subscription)

  }

  trait {:extern "org.reactivestreams.Subscriber"} Subscriber<T> {

    method {:extern} onSubscribe(s: Subscription)
      modifies this

    method {:extern} onNext(t: T)

    method {:extern} onError(t: Throwable)

    method {:extern} onComplete()
  }

  class SequentialSubscriber<T> extends Subscriber<T> {

    var subscription: Subscription?
    var action: Action<StreamEvent<T, Throwable>, ()>

    constructor(a: Action<StreamEvent<T, Throwable>, ()>) {
      this.action := a;
    }

    method {:extern} onSubscribe(s: Subscription) 
      modifies this
    {
      this.subscription := s;
      subscription.request(1);
    }

    method {:extern} {:verify false} onNext(t: T) {
      var _ := action.Call(Some(Success(t)));
      subscription.request(1);
    }

    method {:extern} {:verify false} onError(t: Throwable) {
      var _ := action.Call(Some(Failure(t)));
    }

    method {:extern} {:verify false} onComplete() {
      var _ := action.Call(None);
    }

  }

  method AsSequentialSubscriber<T>(a: Action<StreamEvent<T, Throwable>, ()>) returns (s: Subscriber<T>) {
    s := new SequentialSubscriber(a);
  }

}