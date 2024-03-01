package Signature;

import static Signature.SignatureAlgorithm.signatureAlgorithm;

import Dafny.Aws.Cryptography.Primitives.Types.InternalResult;
import Digest_Compile.ExternDigest;
import Random_Compile.ExternRandom;
import Wrappers_Compile.Result;
import dafny.Array;
import dafny.DafnySequence;
import java.math.BigInteger;
import java.security.GeneralSecurityException;
import java.security.InvalidKeyException;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.security.Signature;
import java.security.SignatureException;
import java.security.interfaces.ECPrivateKey;
import java.security.interfaces.ECPublicKey;
import java.security.spec.ECGenParameterSpec;
import software.amazon.cryptography.primitives.ToDafny;
import software.amazon.cryptography.primitives.internaldafny.types.ECDSASignatureAlgorithm;
import software.amazon.cryptography.primitives.internaldafny.types.Error;
import software.amazon.cryptography.primitives.model.AwsCryptographicPrimitivesError;
import software.amazon.cryptography.primitives.model.OpaqueError;

public class ECDSA extends _ExternBase___default {

  static final String ELLIPTIC_CURVE_ALGORITHM = "EC";
  /* Standards for Efficient Cryptography over a prime field */
  static final String SEC_PRIME_FIELD_PREFIX = "secp";
  static final String SEC_P256 = "256r1";
  static final String SEC_P384 = "384r1";
  /* Constants used by SEC-1 v2 point compression and decompression algorithms */
  static final BigInteger TWO = BigInteger.valueOf(2);
  static final BigInteger THREE = BigInteger.valueOf(3);
  static final BigInteger FOUR = BigInteger.valueOf(4);

  public static Result<SignatureKeyPair, Error> ExternKeyGen(
    ECDSASignatureAlgorithm dtor_signatureAlgorithm
  ) {
    final InternalResult<SignatureAlgorithm, Error> maybeSignatureAlgorithm =
      signatureAlgorithm(dtor_signatureAlgorithm);
    if (maybeSignatureAlgorithm.isFailure()) {
      return CreateExternKeyGenFailure(maybeSignatureAlgorithm.error());
    }
    final ECGenParameterSpec genParameterSpec = new ECGenParameterSpec(
      maybeSignatureAlgorithm.value().curve
    );
    final SecureRandom secureRandom = ExternRandom.getSecureRandom();
    final KeyPairGenerator keyGen;
    try {
      keyGen = KeyPairGenerator.getInstance(ELLIPTIC_CURVE_ALGORITHM);
      keyGen.initialize(genParameterSpec, secureRandom);
    } catch (GeneralSecurityException e) {
      return CreateExternKeyGenFailure(
        ToDafny.Error(
          OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build()
        )
      );
    }
    final KeyPair keyPair = keyGen.generateKeyPair();
    // the verification key is the public key,
    // this is not recorded in the spec,
    // but is implied by the lack of "MUST be kept secret".
    final byte[] verificationKey = PublicKeyUtils.encodeAndCompressPublicKey(
      keyPair.getPublic(),
      dtor_signatureAlgorithm
    );
    // the signing key is the private key, as is implied by:
    // = aws-encryption-sdk-specification/framework/structures.md#signing-key
    // # The value of this key MUST be kept secret.
    final byte[] signingKey = PrivateKeyUtils.encodePrivateKey(
      (ECPrivateKey) keyPair.getPrivate()
    );

    return CreateExternKeyGenSuccess(
      SignatureKeyPair.create(
        DafnySequence.fromBytes(verificationKey),
        DafnySequence.fromBytes(signingKey)
      )
    );
  }

  public static Result<DafnySequence<? extends Byte>, Error> Sign(
    ECDSASignatureAlgorithm dtor_signatureAlgorithm,
    DafnySequence<? extends Byte> dtor_signingKey,
    DafnySequence<? extends Byte> dtor_message
  ) {
    final InternalResult<SignatureAlgorithm, Error> maybeSignatureAlgorithm =
      signatureAlgorithm(dtor_signatureAlgorithm);
    if (maybeSignatureAlgorithm.isFailure()) {
      return CreateSignFailure(maybeSignatureAlgorithm.error());
    }
    SignatureAlgorithm algorithm = maybeSignatureAlgorithm.value();

    final Signature signatureCipher;
    try {
      signatureCipher = Signature.getInstance(algorithm.rawSignatureAlgorithm);
    } catch (NoSuchAlgorithmException ex) {
      return CreateSignFailure(
        ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message(
              String.format(
                "Requested Signature Algorithm is not supported. Requested %s.",
                algorithm.rawSignatureAlgorithm
              )
            )
            .cause(ex)
            .build()
        )
      );
    }

    InternalResult<ECPrivateKey, Error> maybePrivateKey =
      PrivateKeyUtils.decodePrivateKey(algorithm, dtor_signingKey);
    if (maybePrivateKey.isFailure()) {
      return CreateSignFailure(maybePrivateKey.error());
    }
    final ECPrivateKey privateKey = maybePrivateKey.value();

    final InternalResult<byte[], Error> maybeDigest =
      ExternDigest.__default.internalDigest(
        algorithm.messageDigestAlgorithm,
        dtor_message
      );
    if (maybeDigest.isFailure()) {
      return CreateSignFailure(maybeDigest.error());
    }
    final byte[] digest = maybeDigest.value();

    try {
      signatureCipher.initSign(privateKey, ExternRandom.getSecureRandom());
    } catch (InvalidKeyException ex) {
      return CreateSignFailure(
        ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message(
              String.format(
                "Signature Cipher does not support provided key." +
                "Signature %s" +
                "Key %s",
                signatureCipher,
                privateKey
              )
            )
            .cause(ex)
            .build()
        )
      );
    }

    final byte[] signatureBytes;
    try {
      signatureBytes =
        SignUtils.generateEcdsaFixedLengthSignature(
          digest,
          signatureCipher,
          privateKey,
          algorithm.expectedSignatureLength
        );
    } catch (SignatureException e) {
      return CreateSignFailure(
        ToDafny.Error(
          OpaqueError.builder().obj(e).message(e.getMessage()).cause(e).build()
        )
      );
    }
    return CreateSignSuccess(DafnySequence.fromBytes(signatureBytes));
  }

  public static Result<Boolean, Error> Verify(
    ECDSASignatureAlgorithm dtor_signatureAlgorithm,
    DafnySequence<? extends Byte> dtor_verificationKey,
    DafnySequence<? extends Byte> dtor_message,
    DafnySequence<? extends Byte> dtor_signature
  ) {
    final InternalResult<SignatureAlgorithm, Error> maybeSignatureAlgorithm =
      signatureAlgorithm(dtor_signatureAlgorithm);
    if (maybeSignatureAlgorithm.isFailure()) {
      return CreateVerifyFailure(maybeSignatureAlgorithm.error());
    }
    final SignatureAlgorithm algorithm = maybeSignatureAlgorithm.value();

    InternalResult<ECPublicKey, Error> maybePublicKey =
      PublicKeyUtils.decodePublicKey(algorithm, dtor_verificationKey);
    if (maybePublicKey.isFailure()) {
      return CreateVerifyFailure(maybePublicKey.error());
    }
    final ECPublicKey publicKey = maybePublicKey.value();

    final Signature signatureCipher;
    try {
      signatureCipher = Signature.getInstance(algorithm.rawSignatureAlgorithm);
    } catch (NoSuchAlgorithmException ex) {
      return CreateVerifyFailure(
        ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message(
              String.format(
                "Requested Signature Algorithm is not supported. Requested %s.",
                algorithm.rawSignatureAlgorithm
              )
            )
            .cause(ex)
            .build()
        )
      );
    }

    try {
      signatureCipher.initVerify(publicKey);
    } catch (InvalidKeyException ex) {
      return CreateVerifyFailure(
        ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message(
              String.format(
                "Signature does not support provided key." +
                "Signature %s" +
                "Key %s",
                signatureCipher,
                publicKey
              )
            )
            .cause(ex)
            .build()
        )
      );
    }

    final InternalResult<byte[], Error> maybeDigest =
      ExternDigest.__default.internalDigest(
        algorithm.messageDigestAlgorithm,
        dtor_message
      );
    if (maybeDigest.isFailure()) {
      return CreateVerifyFailure(maybeDigest.error());
    }
    final byte[] digest = maybeDigest.value();

    try {
      signatureCipher.update(digest);
    } catch (SignatureException ex) {
      // For `update`, SignatureException can only be thrown if the
      // signature cipher was not initialized.
      // This should be impossible;
      // if it happens, things are very wonky,
      // and we should immediately throw.
      throw new RuntimeException(ex);
    }

    final boolean success;
    try {
      // In the NET Extern,
      // the signature bytes are converted via DER Deserialized.
      // In the ESDK-Java@2.4.0, on decryption,
      // the Signature's bytes are just handed to the cipher.
      // Checking the general Java default provider,
      // sun.security.util.ECUtil.decodeSignature,
      // explicitly states:
      // "Convert the DER encoding of R and S into a concatenation of R and S".
      // Which indicates that this is correct.
      final byte[] signatureAsBytes = (byte[]) Array.unwrap(
        dtor_signature.toArray()
      );
      success = signatureCipher.verify(signatureAsBytes);
    } catch (SignatureException ex) {
      return CreateVerifyFailure(
        ToDafny.Error(
          AwsCryptographicPrimitivesError
            .builder()
            .message(
              String.format(
                "Signature Cipher does not support provided key." +
                "Signature %s" +
                "Key %s",
                signatureCipher,
                publicKey
              )
            )
            .cause(ex)
            .build()
        )
      );
    }

    return CreateVerifySuccess(success);
  }
}
