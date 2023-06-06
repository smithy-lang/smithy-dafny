// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore;

import Wrappers_Compile.Result;
import dafny.Tuple0;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.keystore.internaldafny.KeyStoreClient;
import software.amazon.cryptography.keystore.internaldafny.__default;
import software.amazon.cryptography.keystore.internaldafny.types.Error;
import software.amazon.cryptography.keystore.internaldafny.types.IKeyStoreClient;
import software.amazon.cryptography.keystore.model.BranchKeyStatusResolutionInput;
import software.amazon.cryptography.keystore.model.CreateKeyOutput;
import software.amazon.cryptography.keystore.model.CreateKeyStoreInput;
import software.amazon.cryptography.keystore.model.CreateKeyStoreOutput;
import software.amazon.cryptography.keystore.model.GetActiveBranchKeyInput;
import software.amazon.cryptography.keystore.model.GetActiveBranchKeyOutput;
import software.amazon.cryptography.keystore.model.GetBeaconKeyInput;
import software.amazon.cryptography.keystore.model.GetBeaconKeyOutput;
import software.amazon.cryptography.keystore.model.GetBranchKeyVersionInput;
import software.amazon.cryptography.keystore.model.GetBranchKeyVersionOutput;
import software.amazon.cryptography.keystore.model.GetKeyStoreInfoOutput;
import software.amazon.cryptography.keystore.model.KeyStoreConfig;
import software.amazon.cryptography.keystore.model.VersionKeyInput;

public class KeyStore {
  private final IKeyStoreClient _impl;

  protected KeyStore(BuilderImpl builder) {
    KeyStoreConfig input = builder.KeyStoreConfig();
    software.amazon.cryptography.keystore.internaldafny.types.KeyStoreConfig dafnyValue = ToDafny.KeyStoreConfig(input);
    Result<KeyStoreClient, Error> result = __default.KeyStore(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  KeyStore(IKeyStoreClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  /**
   * In the case that the Key Store contains two ACTIVE Branch Key versions (this should not be possible in normal operation), attempt to resolve to one by making one ACTIVE version DECRYPT_ONLY.
   *
   * @param input Inputs for resolving a multiple ACTIVE versions state.
   *
   */
  public void BranchKeyStatusResolution(BranchKeyStatusResolutionInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.BranchKeyStatusResolutionInput dafnyValue = ToDafny.BranchKeyStatusResolutionInput(input);
    Result<Tuple0, Error> result = this._impl.BranchKeyStatusResolution(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  /**
   * Create a new Branch Key in the Key Store. Additionally create a Beacon Key that is tied to this Branch Key.
   * @return Outputs for Branch Key creation.
   */
  public CreateKeyOutput CreateKey() {
    Result<software.amazon.cryptography.keystore.internaldafny.types.CreateKeyOutput, Error> result = this._impl.CreateKey();
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.CreateKeyOutput(result.dtor_value());
  }

  /**
   * Create the DynamoDB table that backs this Key Store based on the Key Store configuration. If a table already exists, validate it is configured as expected.
   * @return Outputs for Key Store DynamoDB table creation.
   */
  public CreateKeyStoreOutput CreateKeyStore(CreateKeyStoreInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreInput dafnyValue = ToDafny.CreateKeyStoreInput(input);
    Result<software.amazon.cryptography.keystore.internaldafny.types.CreateKeyStoreOutput, Error> result = this._impl.CreateKeyStore(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.CreateKeyStoreOutput(result.dtor_value());
  }

  /**
   * Get the ACTIVE version for a particular Branch Key from the Key Store.
   *
   * @param input Inputs for getting a Branch Key's ACTIVE version.
   * @return Outputs for getting a Branch Key's ACTIVE version.
   */
  public GetActiveBranchKeyOutput GetActiveBranchKey(GetActiveBranchKeyInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyInput dafnyValue = ToDafny.GetActiveBranchKeyInput(input);
    Result<software.amazon.cryptography.keystore.internaldafny.types.GetActiveBranchKeyOutput, Error> result = this._impl.GetActiveBranchKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetActiveBranchKeyOutput(result.dtor_value());
  }

  /**
   * Get a Beacon Key from the Key Store.
   *
   * @param input Inputs for getting a Beacon Key
   * @return Outputs for getting a Beacon Key
   */
  public GetBeaconKeyOutput GetBeaconKey(GetBeaconKeyInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyInput dafnyValue = ToDafny.GetBeaconKeyInput(input);
    Result<software.amazon.cryptography.keystore.internaldafny.types.GetBeaconKeyOutput, Error> result = this._impl.GetBeaconKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBeaconKeyOutput(result.dtor_value());
  }

  /**
   * Get a particular version of a Branch Key from the Key Store.
   *
   * @param input Inputs for getting a version of a Branch Key.
   * @return Outputs for getting a version of a Branch Key.
   */
  public GetBranchKeyVersionOutput GetBranchKeyVersion(GetBranchKeyVersionInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionInput dafnyValue = ToDafny.GetBranchKeyVersionInput(input);
    Result<software.amazon.cryptography.keystore.internaldafny.types.GetBranchKeyVersionOutput, Error> result = this._impl.GetBranchKeyVersion(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetBranchKeyVersionOutput(result.dtor_value());
  }

  /**
   * Returns the configuration information for a Key Store.
   * @return The configuration information for a Key Store.
   */
  public GetKeyStoreInfoOutput GetKeyStoreInfo() {
    Result<software.amazon.cryptography.keystore.internaldafny.types.GetKeyStoreInfoOutput, Error> result = this._impl.GetKeyStoreInfo();
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetKeyStoreInfoOutput(result.dtor_value());
  }

  /**
   * Create a new ACTIVE version of an existing Branch Key in the Key Store, and set the previously ACTIVE version to DECRYPT_ONLY.
   *
   * @param input Inputs for versioning a Branch Key.
   *
   */
  public void VersionKey(VersionKeyInput input) {
    software.amazon.cryptography.keystore.internaldafny.types.VersionKeyInput dafnyValue = ToDafny.VersionKeyInput(input);
    Result<Tuple0, Error> result = this._impl.VersionKey(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
  }

  protected IKeyStoreClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder KeyStoreConfig(KeyStoreConfig KeyStoreConfig);

    KeyStoreConfig KeyStoreConfig();

    KeyStore build();
  }

  static class BuilderImpl implements Builder {
    protected KeyStoreConfig KeyStoreConfig;

    protected BuilderImpl() {
    }

    public Builder KeyStoreConfig(KeyStoreConfig KeyStoreConfig) {
      this.KeyStoreConfig = KeyStoreConfig;
      return this;
    }

    public KeyStoreConfig KeyStoreConfig() {
      return this.KeyStoreConfig;
    }

    public KeyStore build() {
      if (Objects.isNull(this.KeyStoreConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `KeyStoreConfig`");
      }
      return new KeyStore(this);
    }
  }
}
