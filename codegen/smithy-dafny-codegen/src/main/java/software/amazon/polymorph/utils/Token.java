// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import java.util.stream.Stream;

public class Token extends TokenTree {

  public static final Token NEWLINE = Token.of("\n");

  private final CharSequence chars;

  public Token(final CharSequence chars) {
    this.chars = chars;
  }

  public static Token of(char singleChar) {
    return new Token(String.valueOf(singleChar));
  }

  public static Token of(final CharSequence chars) {
    return new Token(chars);
  }

  protected Stream<TokenTree> streamChildren() {
    return Stream.of(this);
  }

  public Boolean isEmpty() {
    return "" == chars || null == chars;
  }

  @Override
  public String toString() {
    return chars == null ? "" : chars.toString();
  }
}
