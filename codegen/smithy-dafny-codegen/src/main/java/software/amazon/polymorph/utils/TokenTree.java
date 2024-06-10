// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import com.google.common.collect.ImmutableList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

/**
 * An immutable rose tree (unbounded branches) for generated code.
 */
public class TokenTree {

  private static final TokenTree EMPTY = new TokenTree();

  private final List<TokenTree> children;

  protected TokenTree() {
    this.children = ImmutableList.of();
  }

  private TokenTree(ImmutableList<TokenTree> children) {
    this.children = children;
  }

  public static TokenTree empty() {
    return EMPTY;
  }

  public static TokenTree of(final TokenTree... trees) {
    return new TokenTree(ImmutableList.copyOf(trees));
  }

  public static TokenTree of(final Stream<TokenTree> trees) {
    return new TokenTree(ImmutableList.copyOf(trees.iterator()));
  }

  public static TokenTree of(final CharSequence... charSequences) {
    return TokenTree.of(Arrays.stream(charSequences).map(Token::of));
  }

  public TokenTree surround(final TokenTree prefix, final TokenTree suffix) {
    return TokenTree.of(prefix, this, suffix);
  }

  public TokenTree braced() {
    return surround(Token.of("{\n"), Token.of("\n}"));
  }

  public TokenTree parenthesized() {
    return surround(Token.of('('), Token.of(')'));
  }

  public TokenTree angleBracketed() {
    return surround(Token.of('<'), Token.of('>'));
  }

  public TokenTree prepend(final TokenTree toPrepend) {
    return TokenTree.of(toPrepend, this);
  }

  public TokenTree append(final TokenTree toAppend) {
    return TokenTree.of(this, toAppend);
  }

  public TokenTree namespaced(final TokenTree namespace) {
    return TokenTree.of(Token.of("namespace"), namespace, this.braced());
  }

  public TokenTree namespaced(final String namespace) {
    return TokenTree.of(
      Token.of("namespace"),
      Token.of(namespace),
      this.braced()
    );
  }

  public TokenTree prependSeperated(final TokenTree separator) {
    Stream<TokenTree> separatedTokens = children
      .stream()
      .flatMap(tokenTree -> Stream.of(separator, tokenTree));
    return new TokenTree(ImmutableList.copyOf(separatedTokens.iterator()));
  }

  public TokenTree separated(final TokenTree separator) {
    if (children.size() < 2) {
      return this;
    }
    Stream<TokenTree> separatedTokens = children
      .stream()
      .flatMap(tokenTree -> Stream.of(separator, tokenTree))
      .skip(1);
    return new TokenTree(ImmutableList.copyOf(separatedTokens.iterator()));
  }

  protected Stream<TokenTree> streamChildren() {
    return children.stream();
  }

  public TokenTree flatten() {
    Stream<TokenTree> flattenChildren = children
      .stream()
      .flatMap(c -> c.streamChildren());
    return new TokenTree(ImmutableList.copyOf(flattenChildren.iterator()));
  }

  public Boolean isEmpty() {
    return 0 == this.children.size();
  }

  public TokenTree prependToNonEmpty(final TokenTree toPrepend) {
    return this.isEmpty() ? this : this.prepend(toPrepend);
  }

  public TokenTree appendToNonEmpty(final TokenTree toPrepend) {
    return this.isEmpty() ? this : this.append(toPrepend);
  }

  public TokenTree dropEmpty() {
    Stream<TokenTree> separatedTokens = children
      .stream()
      .filter(tree -> !tree.isEmpty());
    return new TokenTree(ImmutableList.copyOf(separatedTokens.iterator()));
  }

  public TokenTree lineSeparated() {
    return separated(Token.NEWLINE);
  }

  @Override
  public String toString() {
    if (children.size() == 0) {
      return "";
    }

    final StringBuilder builder = new StringBuilder(children.get(0).toString());
    children
      .stream()
      .skip(1)
      .forEach(tokenTree -> {
        final String treeAsString = tokenTree.toString();
        if (!treeAsString.startsWith("\n")) {
          builder.append(' ');
        }
        builder.append(treeAsString);
      });
    return builder.toString();
  }
}
