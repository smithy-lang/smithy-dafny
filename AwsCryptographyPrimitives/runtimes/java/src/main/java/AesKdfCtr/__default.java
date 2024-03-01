package AesKdfCtr;

import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import java.security.GeneralSecurityException;
import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.model.OpaqueError;

public class __default extends _ExternBase___default {

  public static Wrappers_Compile.Result<
    dafny.DafnySequence<? extends Byte>,
    software.amazon.cryptography.primitives.internaldafny.types.Error
  > AesKdfCtrStream(
    dafny.DafnySequence<? extends Byte> iv,
    dafny.DafnySequence<? extends Byte> key,
    int length
  ) {
    byte[] keyBytes = (byte[]) Array.unwrap(key.toArray());
    byte[] nonceBytes = (byte[]) Array.unwrap(iv.toArray());
    byte[] plaintext = new byte[length];
    try {
      Cipher cipher = Cipher.getInstance("AES/CTR/NoPadding");
      SecretKey secretKey = new SecretKeySpec(keyBytes, "AES");
      IvParameterSpec ivSpec = new IvParameterSpec(nonceBytes);
      cipher.init(Cipher.ENCRYPT_MODE, secretKey, ivSpec);
      byte[] ciphertext = cipher.doFinal(plaintext);
      return CreateStreamSuccess(DafnySequence.fromBytes(ciphertext));
    } catch (GeneralSecurityException e) {
      return CreateStreamFailure(
        ToDafny.Error(OpaqueError.builder().obj(e).build())
      );
    }
  }
}
