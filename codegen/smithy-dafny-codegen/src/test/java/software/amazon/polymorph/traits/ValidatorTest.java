// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.commonmark.node.Node;
import org.commonmark.parser.Parser;
import org.junit.Test;

public class ValidatorTest {

  @Test
  public void TestMarkdown() {
    Parser parser = Parser.builder().build();

    Node document = parser.parse(
      "This is not Markdown\n\nBut it does have paragraphs"
    );
    assertTrue(
      NoMarkupInDocumentationTraitsValidator.isDocumentWithNoMarkup(document)
    );

    document = parser.parse("This is *Markdown*");
    assertFalse(
      NoMarkupInDocumentationTraitsValidator.isDocumentWithNoMarkup(document)
    );
  }
}
