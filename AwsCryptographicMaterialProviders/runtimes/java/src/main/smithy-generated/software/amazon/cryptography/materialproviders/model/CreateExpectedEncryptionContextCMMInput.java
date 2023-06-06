// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.CryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.IKeyring;
import software.amazon.cryptography.materialproviders.Keyring;

/**
 * Inputs for creating an Expected Cryptographic Materials Manager.
 */
public class CreateExpectedEncryptionContextCMMInput {
  /**
   * The Cryprographic Materials Manager that the created Expected Cryptographic Materials Manager will delegate to. Either a Keyring or underlying Cryprographic Materials Manager must be specified.
   */
  private final ICryptographicMaterialsManager underlyingCMM;

  /**
   * The Keyring that the created Cryprographic Materials Manager will use to wrap data keys. The created Expected Encryption Context CMM will delegate to a Default Cryptographic Materials Manager created with this Keyring. Either a Keyring or an underlying Cryprographic Materials Manager must be specified as input.
   */
  private final IKeyring keyring;

  /**
   * A list of Encryption Context keys which are required to be supplied during encryption and decryption, and correspond to Encryption Context key-value pairs which are not stored on the resulting message.
   */
  private final List<String> requiredEncryptionContextKeys;

  protected CreateExpectedEncryptionContextCMMInput(BuilderImpl builder) {
    this.underlyingCMM = builder.underlyingCMM();
    this.keyring = builder.keyring();
    this.requiredEncryptionContextKeys = builder.requiredEncryptionContextKeys();
  }

  /**
   * @return The Cryprographic Materials Manager that the created Expected Cryptographic Materials Manager will delegate to. Either a Keyring or underlying Cryprographic Materials Manager must be specified.
   */
  public ICryptographicMaterialsManager underlyingCMM() {
    return this.underlyingCMM;
  }

  /**
   * @return The Keyring that the created Cryprographic Materials Manager will use to wrap data keys. The created Expected Encryption Context CMM will delegate to a Default Cryptographic Materials Manager created with this Keyring. Either a Keyring or an underlying Cryprographic Materials Manager must be specified as input.
   */
  public IKeyring keyring() {
    return this.keyring;
  }

  /**
   * @return A list of Encryption Context keys which are required to be supplied during encryption and decryption, and correspond to Encryption Context key-value pairs which are not stored on the resulting message.
   */
  public List<String> requiredEncryptionContextKeys() {
    return this.requiredEncryptionContextKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param underlyingCMM The Cryprographic Materials Manager that the created Expected Cryptographic Materials Manager will delegate to. Either a Keyring or underlying Cryprographic Materials Manager must be specified.
     */
    Builder underlyingCMM(ICryptographicMaterialsManager underlyingCMM);

    /**
     * @return The Cryprographic Materials Manager that the created Expected Cryptographic Materials Manager will delegate to. Either a Keyring or underlying Cryprographic Materials Manager must be specified.
     */
    ICryptographicMaterialsManager underlyingCMM();

    /**
     * @param keyring The Keyring that the created Cryprographic Materials Manager will use to wrap data keys. The created Expected Encryption Context CMM will delegate to a Default Cryptographic Materials Manager created with this Keyring. Either a Keyring or an underlying Cryprographic Materials Manager must be specified as input.
     */
    Builder keyring(IKeyring keyring);

    /**
     * @return The Keyring that the created Cryprographic Materials Manager will use to wrap data keys. The created Expected Encryption Context CMM will delegate to a Default Cryptographic Materials Manager created with this Keyring. Either a Keyring or an underlying Cryprographic Materials Manager must be specified as input.
     */
    IKeyring keyring();

    /**
     * @param requiredEncryptionContextKeys A list of Encryption Context keys which are required to be supplied during encryption and decryption, and correspond to Encryption Context key-value pairs which are not stored on the resulting message.
     */
    Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys);

    /**
     * @return A list of Encryption Context keys which are required to be supplied during encryption and decryption, and correspond to Encryption Context key-value pairs which are not stored on the resulting message.
     */
    List<String> requiredEncryptionContextKeys();

    CreateExpectedEncryptionContextCMMInput build();
  }

  static class BuilderImpl implements Builder {
    protected ICryptographicMaterialsManager underlyingCMM;

    protected IKeyring keyring;

    protected List<String> requiredEncryptionContextKeys;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateExpectedEncryptionContextCMMInput model) {
      this.underlyingCMM = model.underlyingCMM();
      this.keyring = model.keyring();
      this.requiredEncryptionContextKeys = model.requiredEncryptionContextKeys();
    }

    public Builder underlyingCMM(ICryptographicMaterialsManager underlyingCMM) {
      this.underlyingCMM = CryptographicMaterialsManager.wrap(underlyingCMM);
      return this;
    }

    public ICryptographicMaterialsManager underlyingCMM() {
      return this.underlyingCMM;
    }

    public Builder keyring(IKeyring keyring) {
      this.keyring = Keyring.wrap(keyring);
      return this;
    }

    public IKeyring keyring() {
      return this.keyring;
    }

    public Builder requiredEncryptionContextKeys(List<String> requiredEncryptionContextKeys) {
      this.requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      return this;
    }

    public List<String> requiredEncryptionContextKeys() {
      return this.requiredEncryptionContextKeys;
    }

    public CreateExpectedEncryptionContextCMMInput build() {
      if (Objects.isNull(this.requiredEncryptionContextKeys()))  {
        throw new IllegalArgumentException("Missing value for required field `requiredEncryptionContextKeys`");
      }
      return new CreateExpectedEncryptionContextCMMInput(this);
    }
  }
}
