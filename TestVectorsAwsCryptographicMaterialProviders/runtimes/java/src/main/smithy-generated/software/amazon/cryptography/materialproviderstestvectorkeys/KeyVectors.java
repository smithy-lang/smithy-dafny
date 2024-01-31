// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.CryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.ICryptographicMaterialsManager;
import software.amazon.cryptography.materialproviders.IKeyring;
import software.amazon.cryptography.materialproviders.Keyring;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.KeyVectorsClient;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.__default;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.Error;
import software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.GetKeyDescriptionInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.GetKeyDescriptionOutput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.KeyVectorsConfig;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.SerializeKeyDescriptionInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.SerializeKeyDescriptionOutput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.TestVectorCmmInput;
import software.amazon.cryptography.materialproviderstestvectorkeys.model.TestVectorKeyringInput;

public class KeyVectors {

  private final IKeyVectorsClient _impl;

  protected KeyVectors(BuilderImpl builder) {
    KeyVectorsConfig input = builder.KeyVectorsConfig();
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.KeyVectorsConfig dafnyValue =
      ToDafny.KeyVectorsConfig(input);
    Result<KeyVectorsClient, Error> result = __default.KeyVectors(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  KeyVectors(IKeyVectorsClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  /**
   * @return Outputs for creating a Keyring.
   */
  public IKeyring CreateTestVectorKeyring(TestVectorKeyringInput input) {
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput dafnyValue =
      ToDafny.TestVectorKeyringInput(input);
    Result<
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring,
      Error
    > result = this._impl.CreateTestVectorKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public ICryptographicMaterialsManager CreateWrappedTestVectorCmm(
    TestVectorCmmInput input
  ) {
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorCmmInput dafnyValue =
      ToDafny.TestVectorCmmInput(input);
    Result<
      software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsManager,
      Error
    > result = this._impl.CreateWrappedTestVectorCmm(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return CryptographicMaterialsManager.wrap(result.dtor_value());
  }

  /**
   * @return Outputs for creating a Keyring.
   */
  public IKeyring CreateWrappedTestVectorKeyring(TestVectorKeyringInput input) {
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.TestVectorKeyringInput dafnyValue =
      ToDafny.TestVectorKeyringInput(input);
    Result<
      software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring,
      Error
    > result = this._impl.CreateWrappedTestVectorKeyring(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return Keyring.wrap(result.dtor_value());
  }

  public GetKeyDescriptionOutput GetKeyDescription(
    GetKeyDescriptionInput input
  ) {
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionInput dafnyValue =
      ToDafny.GetKeyDescriptionInput(input);
    Result<
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.GetKeyDescriptionOutput,
      Error
    > result = this._impl.GetKeyDescription(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetKeyDescriptionOutput(result.dtor_value());
  }

  public SerializeKeyDescriptionOutput SerializeKeyDescription(
    SerializeKeyDescriptionInput input
  ) {
    software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionInput dafnyValue =
      ToDafny.SerializeKeyDescriptionInput(input);
    Result<
      software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.SerializeKeyDescriptionOutput,
      Error
    > result = this._impl.SerializeKeyDescription(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.SerializeKeyDescriptionOutput(result.dtor_value());
  }

  protected IKeyVectorsClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder KeyVectorsConfig(KeyVectorsConfig KeyVectorsConfig);

    KeyVectorsConfig KeyVectorsConfig();

    KeyVectors build();
  }

  static class BuilderImpl implements Builder {

    protected KeyVectorsConfig KeyVectorsConfig;

    protected BuilderImpl() {}

    public Builder KeyVectorsConfig(KeyVectorsConfig KeyVectorsConfig) {
      this.KeyVectorsConfig = KeyVectorsConfig;
      return this;
    }

    public KeyVectorsConfig KeyVectorsConfig() {
      return this.KeyVectorsConfig;
    }

    public KeyVectors build() {
      if (Objects.isNull(this.KeyVectorsConfig())) {
        throw new IllegalArgumentException(
          "Missing value for required field `KeyVectorsConfig`"
        );
      }
      return new KeyVectors(this);
    }
  }
}
