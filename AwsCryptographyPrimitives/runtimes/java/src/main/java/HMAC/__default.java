package HMAC;

import Wrappers_Compile.Result;
import dafny.DafnySequence;
import software.amazon.cryptography.primitives.internaldafny.types.Error;

public class __default extends _ExternBase___default {

  public static Result<DafnySequence<? extends Byte>, Error> Digest(
    software.amazon.cryptography.primitives.internaldafny.types.HMacInput input
  ) {
    Result<HMac, Error> maybeHMac = HMac.Build(input._digestAlgorithm);
    if (maybeHMac.is_Failure()) {
      return CreateDigestFailure(maybeHMac.dtor_error());
    }
    final HMac hmac = maybeHMac.Extract(
      dafny.TypeDescriptor.referenceWithInitializer(HMac.class, () -> null),
      Error._typeDescriptor()
    );
    hmac.Init(input._key);
    hmac.BlockUpdate(input._message);
    final DafnySequence<? extends Byte> output = hmac.GetResult();
    return CreateDigestSuccess(output);
  }
}
