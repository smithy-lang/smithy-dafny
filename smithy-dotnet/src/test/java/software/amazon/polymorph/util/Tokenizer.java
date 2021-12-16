// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.util;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;
import software.amazon.polymorph.antlr.CSharpLexer;

import java.util.List;

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
}
