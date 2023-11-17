// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.IKeyring;
import software.amazon.cryptography.materialproviders.Keyring;

/**
 * Inputs for creating a Multi-Keyring.
 */
public class CreateMultiKeyringInput {

  /**
   * A keyring responsible for wrapping and unwrapping the data key. This is the first keyring that will be used to wrap the data key, and may be responsible for additionally generating the data key.
   */
  private final IKeyring generator;

  /**
   * A list of keyrings (other than the generator) responsible for wrapping and unwrapping the data key.
   */
  private final List<IKeyring> childKeyrings;

  protected CreateMultiKeyringInput(BuilderImpl builder) {
    this.generator = builder.generator();
    this.childKeyrings = builder.childKeyrings();
  }

  /**
   * @return A keyring responsible for wrapping and unwrapping the data key. This is the first keyring that will be used to wrap the data key, and may be responsible for additionally generating the data key.
   */
  public IKeyring generator() {
    return this.generator;
  }

  /**
   * @return A list of keyrings (other than the generator) responsible for wrapping and unwrapping the data key.
   */
  public List<IKeyring> childKeyrings() {
    return this.childKeyrings;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param generator A keyring responsible for wrapping and unwrapping the data key. This is the first keyring that will be used to wrap the data key, and may be responsible for additionally generating the data key.
     */
    Builder generator(IKeyring generator);

    /**
     * @return A keyring responsible for wrapping and unwrapping the data key. This is the first keyring that will be used to wrap the data key, and may be responsible for additionally generating the data key.
     */
    IKeyring generator();

    /**
     * @param childKeyrings A list of keyrings (other than the generator) responsible for wrapping and unwrapping the data key.
     */
    Builder childKeyrings(List<IKeyring> childKeyrings);

    /**
     * @return A list of keyrings (other than the generator) responsible for wrapping and unwrapping the data key.
     */
    List<IKeyring> childKeyrings();

    CreateMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected IKeyring generator;

    protected List<IKeyring> childKeyrings;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateMultiKeyringInput model) {
      this.generator = model.generator();
      this.childKeyrings = model.childKeyrings();
    }

    public Builder generator(IKeyring generator) {
      this.generator = Keyring.wrap(generator);
      return this;
    }

    public IKeyring generator() {
      return this.generator;
    }

    public Builder childKeyrings(List<IKeyring> childKeyrings) {
      this.childKeyrings = childKeyrings;
      return this;
    }

    public List<IKeyring> childKeyrings() {
      return this.childKeyrings;
    }

    public CreateMultiKeyringInput build() {
      if (Objects.isNull(this.childKeyrings())) {
        throw new IllegalArgumentException(
          "Missing value for required field `childKeyrings`"
        );
      }
      return new CreateMultiKeyringInput(this);
    }
  }
}
