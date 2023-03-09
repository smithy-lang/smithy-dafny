// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen.util;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;
import software.amazon.smithy.dafny.codegen.antlr.CSharpLexer;

import java.util.List;

import static org.junit.Assert.assertEquals;

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
                .map(lexeme -> new ParseToken(lexeme.getText(), lexeme.getType())).toList();
    }

    public static record ParseToken(String text, int type) {}

    public static void tokenizeAndAssertEqual(String expected, String actual) {
        final List<ParseToken> actualTokens = tokenize(actual);
        final List<ParseToken> expectedTokens = tokenize(expected);
        assertEquals(expectedTokens, actualTokens);
    }
}
