// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

public enum TypeConversionDirection {
  TO_DAFNY,
  FROM_DAFNY;

  @Override
  public String toString() {
    return switch (this) {
      case TO_DAFNY -> "ToDafny";
      case FROM_DAFNY -> "FromDafny";
    };
  }
}
