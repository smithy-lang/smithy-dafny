// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.codegen;

import java.util.Objects;

public enum DafnyClientCodegenEdition {
  // Java identifiers (including enum values) cannot start with a number, but edition names are typically numeric.
  EDITION_2023,
  EDITION_2023_10; // 2023.10

  /**
   * Returns the enum value corresponding to the given numeric string, e.g. "2023".
   *
   * @throws IllegalArgumentException if there is no corresponding edition
   */
  public static DafnyClientCodegenEdition fromNumeric(final String edition) {
    Objects.requireNonNull(edition);
    return DafnyClientCodegenEdition.valueOf(
      "EDITION_" + edition.replace(".", "_")
    );
  }
}
