// Class ActionPublisher
// Dafny class ActionPublisher compiled into Java
package StandardLibraryJavaConversions_Compile;

import Wrappers_Compile.*;
import StandardLibrary_Compile.UInt_Compile.*;
import StandardLibrary_Compile.Actions_Compile.*;
import StandardLibrary_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class ActionPublisher<T> implements org.reactivestreams.Publisher<T> {
  protected dafny.TypeDescriptor<T> _td_T;
  public ActionPublisher(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._subscribeAction = null;
  }
  public void __ctor(StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> subscribeAction)
  {
    (this)._subscribeAction = subscribeAction;
  }
  public void subscribe(org.reactivestreams.Subscriber<T> s)
  {
    SubscriberAction<T> _106_action;
    SubscriberAction<T> _nw4 = new SubscriberAction<T>(_td_T);
    _nw4.__ctor(s);
    _106_action = _nw4;
    dafny.Tuple0 _107___v3;
    dafny.Tuple0 _out12;
    _out12 = ((this).subscribeAction()).Call(_106_action);
    _107___v3 = _out12;
  }
  public StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> _subscribeAction;
  public StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> subscribeAction()
  {
    return this._subscribeAction;
  }
  @Override
  public java.lang.String toString() {
    return "StandardLibraryJavaConversions.ActionPublisher";
  }
}
