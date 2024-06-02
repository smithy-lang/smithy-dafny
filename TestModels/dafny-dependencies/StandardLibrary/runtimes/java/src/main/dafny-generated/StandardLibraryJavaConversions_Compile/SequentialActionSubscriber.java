// Class SequentialActionSubscriber
// Dafny class SequentialActionSubscriber compiled into Java
package StandardLibraryJavaConversions_Compile;

import Wrappers_Compile.*;
import StandardLibrary_Compile.UInt_Compile.*;
import StandardLibrary_Compile.Actions_Compile.*;
import StandardLibrary_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SequentialActionSubscriber<T> implements org.reactivestreams.Subscriber<T> {
  protected dafny.TypeDescriptor<T> _td_T;
  public SequentialActionSubscriber(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this.subscription = (org.reactivestreams.Subscription) null;
    this.action = null;
  }
  public org.reactivestreams.Subscription subscription;
  public StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0> action;
  public void __ctor(StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<T, java.lang.Throwable>>, dafny.Tuple0> a)
  {
    (this).action = a;
  }
  public void onSubscribe(org.reactivestreams.Subscription s)
  {
    (this).subscription = s;
    (this.subscription).request((long) 1L);
  }
  public void onNext(T t)
  {
    dafny.Tuple0 _97___v0;
    dafny.Tuple0 _out8;
    _out8 = (this.action).Call(Wrappers_Compile.Option.<Wrappers_Compile.Result<T, java.lang.Throwable>>create_Some(Wrappers_Compile.Result.<T, java.lang.Throwable>_typeDescriptor(_td_T, ((dafny.TypeDescriptor<java.lang.Throwable>)(java.lang.Object)dafny.TypeDescriptor.reference(java.lang.Throwable.class))), Wrappers_Compile.Result.<T, java.lang.Throwable>create_Success(_td_T, ((dafny.TypeDescriptor<java.lang.Throwable>)(java.lang.Object)dafny.TypeDescriptor.reference(java.lang.Throwable.class)), t)));
    _97___v0 = _out8;
    (this.subscription).request((long) 1L);
  }
  public void onError(java.lang.Throwable t)
  {
    dafny.Tuple0 _98___v1;
    dafny.Tuple0 _out9;
    _out9 = (this.action).Call(Wrappers_Compile.Option.<Wrappers_Compile.Result<T, java.lang.Throwable>>create_Some(Wrappers_Compile.Result.<T, java.lang.Throwable>_typeDescriptor(_td_T, ((dafny.TypeDescriptor<java.lang.Throwable>)(java.lang.Object)dafny.TypeDescriptor.reference(java.lang.Throwable.class))), Wrappers_Compile.Result.<T, java.lang.Throwable>create_Failure(_td_T, ((dafny.TypeDescriptor<java.lang.Throwable>)(java.lang.Object)dafny.TypeDescriptor.reference(java.lang.Throwable.class)), t)));
    _98___v1 = _out9;
  }
  public void onComplete()
  {
    dafny.Tuple0 _99___v2;
    dafny.Tuple0 _out10;
    _out10 = (this.action).Call(Wrappers_Compile.Option.<Wrappers_Compile.Result<T, java.lang.Throwable>>create_None(Wrappers_Compile.Result.<T, java.lang.Throwable>_typeDescriptor(_td_T, ((dafny.TypeDescriptor<java.lang.Throwable>)(java.lang.Object)dafny.TypeDescriptor.reference(java.lang.Throwable.class)))));
    _99___v2 = _out10;
  }
  @Override
  public java.lang.String toString() {
    return "StandardLibraryJavaConversions.SequentialActionSubscriber";
  }
}
