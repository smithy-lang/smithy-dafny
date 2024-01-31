// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

public enum CmmOperation {
  ENCRYPT("ENCRYPT"),

  DECRYPT("DECRYPT");

  private final String value;

  private CmmOperation(String value) {
    this.value = value;
  }

  public String toString() {
    return String.valueOf(value);
  }
}
