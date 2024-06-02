// Class SubscriberAction
// Dafny class SubscriberAction compiled into Java
package StandardLibraryJavaConversions_Compile;

import Wrappers_Compile.*;
import StandardLibrary_Compile.UInt_Compile.*;
import StandardLibrary_Compile.Actions_Compile.*;
import StandardLibrary_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SubscriberAction<T> implements StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0> {
  protected dafny.TypeDescriptor<T> _td_T;
  public SubscriberAction(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._Repr = dafny.DafnySet.<Object> empty();
    this._subscriber = null;
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
  public void __ctor(org.reactivestreams.Subscriber<T> subscriber)
  {
    (this)._subscriber = subscriber;
  }
  public dafny.Tuple0 Call(Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>> e)
  {
    dafny.Tuple0 nothing = dafny.Tuple0.Default();
    Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>> _source5 = e;
    if (_source5.is_None()) {
      {
        ((this).subscriber()).onComplete();
      }
    } else {
      Wrappers_Compile.Result<T, java.lang.Throwable> _101___mcc_h0 = ((Wrappers_Compile.Option_Some<Wrappers_Compile.Result<T, java.lang.Throwable>>)_source5)._value;
      Wrappers_Compile.Result<T, java.lang.Throwable> _source6 = _101___mcc_h0;
      if (_source6.is_Success()) {
        T _102___mcc_h1 = ((Wrappers_Compile.Result_Success<T, java.lang.Throwable>)_source6)._value;
        T _103_value = _102___mcc_h1;
        {
          ((this).subscriber()).onNext(_103_value);
        }
      } else {
        java.lang.Throwable _104___mcc_h2 = ((Wrappers_Compile.Result_Failure<T, java.lang.Throwable>)_source6)._error;
        java.lang.Throwable _105_throwable = _104___mcc_h2;
        {
          ((this).subscriber()).onError(_105_throwable);
        }
      }
    }
    nothing = dafny.Tuple0.create();
    return nothing;
  }
  public org.reactivestreams.Subscriber<T> _subscriber;
  public org.reactivestreams.Subscriber<T> subscriber()
  {
    return this._subscriber;
  }
  @Override
  public java.lang.String toString() {
    return "StandardLibraryJavaConversions.SubscriberAction";
  }
}
