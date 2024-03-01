package Digest_Compile;

import Dafny.Aws.Cryptography.Primitives.Types.InternalResult;
import ExternDigest._ExternBase___default;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.internaldafny.types.DigestAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.Error;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;

public class ExternDigest {

  public static class __default extends _ExternBase___default {

    public static Result<DafnySequence<? extends Byte>, Error> Digest(
      DigestAlgorithm digestAlgorithm,
      DafnySequence<? extends Byte> dtor_message
    ) {
      final InternalResult<byte[], Error> maybeDigest = internalDigest(
        digestAlgorithm,
        dtor_message
      );
      if (maybeDigest.isFailure()) {
        return CreateDigestFailure(maybeDigest.error());
      }
      return CreateDigestSuccess(DafnySequence.fromBytes(maybeDigest.value()));
    }

    public static InternalResult<byte[], Error> internalDigest(
      DigestAlgorithm digestAlgorithm,
      DafnySequence<? extends Byte> dtor_message
    ) {
      try {
        final MessageDigest hash = getHash(digestAlgorithm);
        final byte[] messageBytes = (byte[]) Array.unwrap(
          dtor_message.toArray()
        );
        hash.update(messageBytes);
        final byte[] digest = hash.digest();
        return InternalResult.success(digest);
      } catch (NoSuchAlgorithmException ex) {
        final Error err = ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message("Requested digest Algorithm is not supported.")
            .cause(ex)
            .build()
        );
        return InternalResult.failure(err);
      }
    }

    private static MessageDigest getHash(DigestAlgorithm digestAlgorithm)
      throws NoSuchAlgorithmException {
      if (digestAlgorithm.is_SHA__256()) {
        return MessageDigest.getInstance("SHA-256");
      } else if (digestAlgorithm.is_SHA__384()) {
        return MessageDigest.getInstance("SHA-384");
      } else if (digestAlgorithm.is_SHA__512()) {
        return MessageDigest.getInstance("SHA-512");
      } else {
        throw new NoSuchAlgorithmException();
      }
    }
  }
}
