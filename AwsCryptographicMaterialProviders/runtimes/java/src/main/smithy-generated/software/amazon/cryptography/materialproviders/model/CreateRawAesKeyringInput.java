// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.Objects;

/**
 * Inputs for creating a Raw AES Keyring.
 */
public class CreateRawAesKeyringInput {

  /**
   * A namespace associated with this wrapping key.
   */
  private final String keyNamespace;

  /**
   * A name associated with this wrapping key.
   */
  private final String keyName;

  /**
   * The AES key used with AES_GCM encryption and decryption.
   */
  private final ByteBuffer wrappingKey;

  /**
   * The AES_GCM algorithm this Keyring uses to wrap and unwrap data keys.
   */
  private final AesWrappingAlg wrappingAlg;

  protected CreateRawAesKeyringInput(BuilderImpl builder) {
    this.keyNamespace = builder.keyNamespace();
    this.keyName = builder.keyName();
    this.wrappingKey = builder.wrappingKey();
    this.wrappingAlg = builder.wrappingAlg();
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
   * @return The AES key used with AES_GCM encryption and decryption.
   */
  public ByteBuffer wrappingKey() {
    return this.wrappingKey;
  }

  /**
   * @return The AES_GCM algorithm this Keyring uses to wrap and unwrap data keys.
   */
  public AesWrappingAlg wrappingAlg() {
    return this.wrappingAlg;
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
     * @param wrappingKey The AES key used with AES_GCM encryption and decryption.
     */
    Builder wrappingKey(ByteBuffer wrappingKey);

    /**
     * @return The AES key used with AES_GCM encryption and decryption.
     */
    ByteBuffer wrappingKey();

    /**
     * @param wrappingAlg The AES_GCM algorithm this Keyring uses to wrap and unwrap data keys.
     */
    Builder wrappingAlg(AesWrappingAlg wrappingAlg);

    /**
     * @return The AES_GCM algorithm this Keyring uses to wrap and unwrap data keys.
     */
    AesWrappingAlg wrappingAlg();

    CreateRawAesKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected String keyNamespace;

    protected String keyName;

    protected ByteBuffer wrappingKey;

    protected AesWrappingAlg wrappingAlg;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateRawAesKeyringInput model) {
      this.keyNamespace = model.keyNamespace();
      this.keyName = model.keyName();
      this.wrappingKey = model.wrappingKey();
      this.wrappingAlg = model.wrappingAlg();
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

    public Builder wrappingKey(ByteBuffer wrappingKey) {
      this.wrappingKey = wrappingKey;
      return this;
    }

    public ByteBuffer wrappingKey() {
      return this.wrappingKey;
    }

    public Builder wrappingAlg(AesWrappingAlg wrappingAlg) {
      this.wrappingAlg = wrappingAlg;
      return this;
    }

    public AesWrappingAlg wrappingAlg() {
      return this.wrappingAlg;
    }

    public CreateRawAesKeyringInput build() {
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
      if (Objects.isNull(this.wrappingKey())) {
        throw new IllegalArgumentException(
          "Missing value for required field `wrappingKey`"
        );
      }
      if (Objects.isNull(this.wrappingAlg())) {
        throw new IllegalArgumentException(
          "Missing value for required field `wrappingAlg`"
        );
      }
      return new CreateRawAesKeyringInput(this);
    }
  }
}
