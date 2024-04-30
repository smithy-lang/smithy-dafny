// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.util;

import java.util.List;
import java.util.Objects;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;
import org.junit.Assert;
import software.amazon.polymorph.antlr.CSharpLexer;

/**
 * Simple tokenizer for C# source code, intended for testing generated code in a format-agnostic manner.
 * Uses the ANTLR-generated parser.
 */
public class Tokenizer {

  public static List<ParseToken> tokenize(final String source) {
    final CharStream charStream = CharStreams.fromString(source);
    final Lexer lexer = new CSharpLexer(charStream);
    final List<? extends Token> lexemes = lexer.getAllTokens();
    return lexemes
      .stream()
      .filter(lexeme -> lexeme.getType() != CSharpLexer.WHITESPACES)
      .map(lexeme -> new ParseToken(lexeme.getText(), lexeme.getType()))
      .toList();
  }

  public static record ParseToken(String text, int type) {}

  public static void tokenizeAndAssertEqual(String expected, String actual) {
    final List<ParseToken> actualTokens = tokenize(actual);
    final List<ParseToken> expectedTokens = tokenize(expected);
    if (!Objects.equals(expectedTokens, actualTokens)) {
      // If the tokens aren't equal, assert the original strings are equal
      // knowing it is guaranteed to fail,
      // just so that we get a much more readable diff in tooling.
      Assert.assertEquals(expected, actual);
    }
  }
}
