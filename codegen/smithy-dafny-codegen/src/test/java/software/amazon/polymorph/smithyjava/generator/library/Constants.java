// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

class Constants {

  static String RANGE_TRAIT_INTEGER_BUILD_METHOD_START =
    "public TestRangeMinMaxInteger build()";
  static String RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN =
    "return new TestRangeMinMaxInteger(this);";
  static String RANGE_TRAIT_INTEGER_BUILD_EXPECTED =
    """
    %s {
      if (Objects.nonNull(this.zeroToTen()) && this.zeroToTen() < 0) {
        throw new IllegalArgumentException("`zeroToTen` must be greater than or equal to 0");
      }
      if (Objects.nonNull(this.zeroToTen()) && this.zeroToTen() > 10) {
        throw new IllegalArgumentException("`zeroToTen` must be less than or equal to 10.");
      }
      %s
    }""".formatted(
        RANGE_TRAIT_INTEGER_BUILD_METHOD_START,
        RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN
      );

  // Method's end is down 1 line (1 \n), in class (2 spaces), inside BuilderImpl (2 spaces), and the bracket (1 } )
  static int BUILD_METHOD_END_OFFSET = 6;

  static String LENGTH_TRAIT_BLOB_BUILD_METHOD_START =
    "public TestLengthMinMaxBlob build()";
  static String LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN =
    "return new TestLengthMinMaxBlob(this);";
  static String LENGTH_TRAIT_BLOB_BUILD_METHOD_EXPECTED =
    """
    %s {
      if (Objects.nonNull(this.key()) && this.key().remaining() < 256) {
        throw new IllegalArgumentException("The size of `key` must be greater than or equal to 256");
      }
      if (Objects.nonNull(this.key()) && this.key().remaining() > 256) {
        throw new IllegalArgumentException("The size of `key` must be less than or equal to 256");
      }
      %s
    }
    """.formatted(
        LENGTH_TRAIT_BLOB_BUILD_METHOD_START,
        LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN
      );
}
