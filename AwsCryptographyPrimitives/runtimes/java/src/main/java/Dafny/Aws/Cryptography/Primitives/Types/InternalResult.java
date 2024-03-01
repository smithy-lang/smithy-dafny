package Dafny.Aws.Cryptography.Primitives.Types;

/**
 * Similar to the translation of Dafny's Wrappers.Result type,
 * but without the complexity of dealing with TypeDescriptors.
 * The former is necessary when extern methods need to return
 * results to Dafny code, but InteralResult is easier to work with
 * when just passing results between internal helper methods.
 *
 * This class was created mainly to ease refactorings.
 * New code should strongly consider using Java exceptions
 * idiomatically instead.
 */
public class InternalResult<T, E> {

  private final boolean isSuccess;
  private final T value;
  private final E error;

  private InternalResult(boolean isSuccess, T value, E error) {
    this.isSuccess = isSuccess;
    this.value = value;
    this.error = error;
  }

  public static <T, E> InternalResult success(T t) {
    return new InternalResult(true, t, null);
  }

  public static <T, E> InternalResult failure(E e) {
    return new InternalResult(false, null, e);
  }

  public boolean isSuccess() {
    return isSuccess;
  }

  public boolean isFailure() {
    return !isSuccess;
  }

  public T value() {
    if (!isSuccess) {
      throw new IllegalStateException(
        "Tried to extract a value from a failure: " + this
      );
    }
    return value;
  }

  public E error() {
    if (isSuccess) {
      throw new IllegalStateException(
        "Tried to extract an error from a success: " + this
      );
    }
    return error;
  }
}
