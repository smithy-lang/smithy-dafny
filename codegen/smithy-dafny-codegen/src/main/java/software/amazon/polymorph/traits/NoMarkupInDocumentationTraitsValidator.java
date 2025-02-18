// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import org.commonmark.node.Document;
import org.commonmark.node.Node;
import org.commonmark.node.Paragraph;
import org.commonmark.node.SoftLineBreak;
import org.commonmark.node.Text;
import org.commonmark.parser.Parser;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.neighbor.Walker;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.ValidationEvent;

public class NoMarkupInDocumentationTraitsValidator extends AbstractValidator {

  @Override
  public List<ValidationEvent> validate(Model model) {
    List<ValidationEvent> events = new ArrayList<>();
    Parser parser = Parser.builder().build();

    // We only check shapes in the closure of local services for now.
    // That's adequate because we only generate documentation for local services so far.
    // We could generate documentation for wrapped AWS SDKs in Dafny source code as well,
    // but then we'll have to support markdown since the AWS service models
    // will definitely have markdown.
    for (Shape localService : model.getShapesWithTrait(
      LocalServiceTrait.class
    )) {
      for (Shape shape : new Walker(model).walkShapes(localService)) {
        // We may hit shapes in other services, especially AWS services.
        // We don't want to warn against those shapes since they aren't in the scope
        // of what we're generating.
        // Note a more robust way to distinguish the scope of which shapes
        // we're generating vs just importing is to use the
        // "sources" vs. "imports" concept for Smithy build plugins:
        // https://smithy.io/2.0/guides/smithy-build-json.html#using-smithy-build-json
        if (
          !ModelUtils.isInServiceNamespace(shape, (ServiceShape) localService)
        ) {
          continue;
        }

        var trait = shape.getTrait(DocumentationTrait.class);
        if (trait.isPresent()) {
          String docContent = trait.get().getValue();
          if (docContent.startsWith("/")) {
            events.add(
              danger(
                shape,
                "@documentation content should not start with a '/'. " +
                "This most likely happened because the source file is trying to use \"////...\" as a visual delimiter, " +
                "but three consecutive slashes is always interpreted as @documentation."
              )
            );
          }

          Node document = parser.parse(docContent);
          if (!containsNoMarkup(document)) {
            events.add(
              warning(
                shape,
                "smithy-dafny currently only supports @documentation with plaintext content, but this shape's documentation contains markdown."
              )
            );
          }
        }
      }
    }
    return events;
  }

  public static boolean containsNoMarkup(Node node) {
    if (
      !(node instanceof Document ||
        node instanceof Paragraph ||
        node instanceof Text ||
        node instanceof SoftLineBreak)
    ) {
      return false;
    }

    for (var child : new NodeChildren(node)) {
      if (!containsNoMarkup(child)) {
        return false;
      }
    }

    return true;
  }

  private record NodeChildren(Node parent) implements Iterable<Node> {
    @Override
    public Iterator<Node> iterator() {
      return new NodeIterator(parent.getFirstChild());
    }
  }

  private static class NodeIterator implements Iterator<Node> {

    private Node next;

    public NodeIterator(Node first) {
      this.next = first;
    }

    @Override
    public boolean hasNext() {
      return next != null;
    }

    @Override
    public Node next() {
      var result = next;
      next = next.getNext();
      return result;
    }
  }
}
