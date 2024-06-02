// Class SubscribingAction
// Dafny class SubscribingAction compiled into Java
package StandardLibraryJavaConversions_Compile;

import Wrappers_Compile.*;
import StandardLibrary_Compile.UInt_Compile.*;
import StandardLibrary_Compile.Actions_Compile.*;
import StandardLibrary_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SubscribingAction<T> implements StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> {
  protected dafny.TypeDescriptor<T> _td_T;
  public SubscribingAction(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._Repr = dafny.DafnySet.<Object> empty();
    this._publisher = null;
  }
  public dafny.DafnySet<? extends Object> _Repr;
  public dafny.DafnySet<? extends Object> Repr()
  {
    return this._Repr;
  }
  public void set_Repr(dafny.DafnySet<? extends Object> value)
  {
    this._Repr = value;
  }
  public void __ctor(org.reactivestreams.Publisher<T> publisher)
  {
    (this)._publisher = publisher;
  }
  public dafny.Tuple0 Call(StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0> a)
  {
    dafny.Tuple0 nothing = dafny.Tuple0.Default();
    org.reactivestreams.Subscriber<T> _100_subscriber;
    org.reactivestreams.Subscriber<T> _out11;
    _out11 = __default.<T>AsSequentialSubscriber(_td_T, a);
    _100_subscriber = _out11;
    ((this).publisher()).subscribe(_100_subscriber);
    nothing = dafny.Tuple0.create();
    return nothing;
  }
  public org.reactivestreams.Publisher<T> _publisher;
  public org.reactivestreams.Publisher<T> publisher()
  {
    return this._publisher;
  }
  @Override
  public java.lang.String toString() {
    return "StandardLibraryJavaConversions.SubscribingAction";
  }
}
