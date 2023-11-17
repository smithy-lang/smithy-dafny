// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

/**
 * Inputs for creating a Raw RAW Keyring.
 */
public class CreateRawRsaKeyringInput {

  /**
   * A namespace associated with this wrapping key.
   */
  private final String keyNamespace;

  /**
   * A name associated with this wrapping key.
   */
  private final String keyName;

  /**
   * The RSA padding scheme to use with this keyring.
   */
  private final PaddingScheme paddingScheme;

  /**
   * The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. If not specified, this Keyring cannot be used on encrypt. A public key and/or a private key must be specified.
   */
  private final ByteBuffer publicKey;

  /**
   * The private RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded PKCS #8 PrivateKeyInfo structure. If not specified, this Keyring cannot be used on decrypt. A public key and/or a private key must be specified.
   */
  private final ByteBuffer privateKey;

  protected CreateRawRsaKeyringInput(BuilderImpl builder) {
    this.keyNamespace = builder.keyNamespace();
    this.keyName = builder.keyName();
    this.paddingScheme = builder.paddingScheme();
    this.publicKey = builder.publicKey();
    this.privateKey = builder.privateKey();
  }

  /**
   * @return A namespace associated with this wrapping key.
   */
  public String keyNamespace() {
    return this.keyNamespace;
  }

  /**
   * @return A name associated with this wrapping key.
   */
  public String keyName() {
    return this.keyName;
  }

  /**
   * @return The RSA padding scheme to use with this keyring.
   */
  public PaddingScheme paddingScheme() {
    return this.paddingScheme;
  }

  /**
   * @return The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. If not specified, this Keyring cannot be used on encrypt. A public key and/or a private key must be specified.
   */
  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  /**
   * @return The private RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded PKCS #8 PrivateKeyInfo structure. If not specified, this Keyring cannot be used on decrypt. A public key and/or a private key must be specified.
   */
  public ByteBuffer privateKey() {
    return this.privateKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param keyNamespace A namespace associated with this wrapping key.
     */
    Builder keyNamespace(String keyNamespace);

    /**
     * @return A namespace associated with this wrapping key.
     */
    String keyNamespace();

    /**
     * @param keyName A name associated with this wrapping key.
     */
    Builder keyName(String keyName);

    /**
     * @return A name associated with this wrapping key.
     */
    String keyName();

    /**
     * @param paddingScheme The RSA padding scheme to use with this keyring.
     */
    Builder paddingScheme(PaddingScheme paddingScheme);

    /**
     * @return The RSA padding scheme to use with this keyring.
     */
    PaddingScheme paddingScheme();

    /**
     * @param publicKey The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. If not specified, this Keyring cannot be used on encrypt. A public key and/or a private key must be specified.
     */
    Builder publicKey(ByteBuffer publicKey);

    /**
     * @return The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. If not specified, this Keyring cannot be used on encrypt. A public key and/or a private key must be specified.
     */
    ByteBuffer publicKey();

    /**
     * @param privateKey The private RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded PKCS #8 PrivateKeyInfo structure. If not specified, this Keyring cannot be used on decrypt. A public key and/or a private key must be specified.
     */
    Builder privateKey(ByteBuffer privateKey);

    /**
     * @return The private RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded PKCS #8 PrivateKeyInfo structure. If not specified, this Keyring cannot be used on decrypt. A public key and/or a private key must be specified.
     */
    ByteBuffer privateKey();

    CreateRawRsaKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected String keyNamespace;

    protected String keyName;

    protected PaddingScheme paddingScheme;

    protected ByteBuffer publicKey;

    protected ByteBuffer privateKey;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateRawRsaKeyringInput model) {
      this.keyNamespace = model.keyNamespace();
      this.keyName = model.keyName();
      this.paddingScheme = model.paddingScheme();
      this.publicKey = model.publicKey();
      this.privateKey = model.privateKey();
    }

    public Builder keyNamespace(String keyNamespace) {
      this.keyNamespace = keyNamespace;
      return this;
    }

    public String keyNamespace() {
      return this.keyNamespace;
    }

    public Builder keyName(String keyName) {
      this.keyName = keyName;
      return this;
    }

    public String keyName() {
      return this.keyName;
    }

    public Builder paddingScheme(PaddingScheme paddingScheme) {
      this.paddingScheme = paddingScheme;
      return this;
    }

    public PaddingScheme paddingScheme() {
      return this.paddingScheme;
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public Builder privateKey(ByteBuffer privateKey) {
      this.privateKey = privateKey;
      return this;
    }

    public ByteBuffer privateKey() {
      return this.privateKey;
    }

    public CreateRawRsaKeyringInput build() {
      if (Objects.isNull(this.keyNamespace())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyNamespace`"
        );
      }
      if (Objects.isNull(this.keyName())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyName`"
        );
      }
      if (Objects.isNull(this.paddingScheme())) {
        throw new IllegalArgumentException(
          "Missing value for required field `paddingScheme`"
        );
      }
      return new CreateRawRsaKeyringInput(this);
    }
  }
}
