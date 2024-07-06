// Class __default
// Dafny class __default compiled into Java
package StandardLibraryJavaConversions_Compile;

import Wrappers_Compile.*;
import StandardLibrary_Compile.UInt_Compile.*;
import StandardLibrary_Compile.Actions_Compile.*;
import StandardLibrary_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__T> org.reactivestreams.Subscriber<__T> AsSequentialSubscriber(dafny.TypeDescriptor<__T> _td___T, StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<__T, java.lang.Throwable>>, dafny.Tuple0> a)
  {
    org.reactivestreams.Subscriber<__T> s = null;
    if(true) {
      SequentialActionSubscriber<__T> _nw1 = new SequentialActionSubscriber<__T>(_td___T);
      _nw1.__ctor(a);
      s = _nw1;
    }
    return s;
  }
  public static <__T> StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<__T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> AsStream(dafny.TypeDescriptor<__T> _td___T, org.reactivestreams.Publisher<__T> p)
  {
    StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<__T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> s = null;
    if(true) {
      SubscribingAction<__T> _nw2 = new SubscribingAction<__T>(_td___T);
      _nw2.__ctor(p);
      s = _nw2;
    }
    return s;
  }
  public static <__T> org.reactivestreams.Publisher<__T> AsPublisher(dafny.TypeDescriptor<__T> _td___T, StandardLibrary_Compile.Actions_Compile.Action<StandardLibrary_Compile.Actions_Compile.Action<Wrappers_Compile.Option<Wrappers_Compile.Result<__T, java.lang.Throwable>>, dafny.Tuple0>, dafny.Tuple0> a)
  {
    org.reactivestreams.Publisher<__T> s = null;
    if(true) {
      ActionPublisher<__T> _nw3 = new ActionPublisher<__T>(_td___T);
      _nw3.__ctor(a);
      s = _nw3;
    }
    return s;
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> AsBytesRemaining(java.nio.ByteBuffer bb)
  {
    dafny.DafnySequence<? extends java.lang.Byte> res = dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor());
    if(true) {
      int _89_length;
      _89_length = (bb).remaining();
      int _90_start;
      _90_start = (bb).position();
      res = dafny.DafnySequence.Create(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor(), java.math.BigInteger.valueOf(_89_length), ((dafny.Function3<java.nio.ByteBuffer, java.lang.Integer, java.lang.Integer, java.util.function.Function<java.math.BigInteger, java.lang.Byte>>)(_91_bb, _92_start, _93_length) -> ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_94_i_boxed0) -> {
        java.math.BigInteger _94_i = ((java.math.BigInteger)(java.lang.Object)(_94_i_boxed0));
        return (_91_bb).get((int) (((_94_i).intValue()) + (_92_start)));
      })).apply(bb, _90_start, _89_length));
    }
    return res;
  }
  public static java.nio.ByteBuffer ToByteBuffer(dafny.DafnySequence<? extends java.lang.Byte> b)
  {
    java.nio.ByteBuffer res = null;
    if(true) {
      int _95_length;
      _95_length = (b).cardinalityInt();
      java.nio.ByteBuffer _out7;
      _out7 = StandardLibraryJavaConversions_Compile._Companion_java.nio.ByteBuffer.allocate(_95_length);
      res = _out7;
      int _hi1 = _95_length;
      for (int _96_i = 0; _96_i < _hi1; _96_i++) {
        (res).put(((byte)(java.lang.Object)((b).select(_96_i))));
      }
    }
    return res;
  }
  @Override
  public java.lang.String toString() {
    return "StandardLibraryJavaConversions._default";
  }
}
