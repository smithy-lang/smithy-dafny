package ConcurrentCall;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class __default {

  public __default() {}

  public static void ConcurrentCall(
    Callee callee,
    int serialIters,
    int concurrentIters
  ) {
    ExecutorService pool = Executors.newFixedThreadPool(concurrentIters);
    for (int i = 0; i < concurrentIters; i++) {
      final int ii = i;
      pool.execute(() -> {
        for (int j = 0; j < serialIters; ++j) {
          callee.call(j, ii);
        }
      });
    }
    pool.shutdown();
    try {
      pool.awaitTermination(120, TimeUnit.SECONDS);
    } catch (Exception e) {}
  }

  private static final dafny.TypeDescriptor<__default> _TYPE =
    dafny.TypeDescriptor.<__default>referenceWithInitializer(
      __default.class,
      () -> (__default) null
    );

  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }

  @Override
  public java.lang.String toString() {
    return "ConcurrentCall._default";
  }
}
