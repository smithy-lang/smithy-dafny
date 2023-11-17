// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdInput;
import software.amazon.cryptography.materialproviders.model.GetBranchKeyIdOutput;

public interface IBranchKeyIdSupplier {
  /**
   * Given the Encryption Context associated with this encryption or decryption, returns the branch key that should be responsible for unwrapping or wrapping the data key.
   *
   * @param input Inputs for determining the Branch Key which should be used to wrap or unwrap the data key for this encryption or decryption
   * @return Outputs for the Branch Key responsible for wrapping or unwrapping the data key in this encryption or decryption.
   */
  GetBranchKeyIdOutput GetBranchKeyId(GetBranchKeyIdInput input);
}
