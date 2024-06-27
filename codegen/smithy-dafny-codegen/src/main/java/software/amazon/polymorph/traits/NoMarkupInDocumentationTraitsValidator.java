package software.amazon.polymorph.traits;

import org.commonmark.node.Document;
import org.commonmark.node.Node;
import org.commonmark.node.Paragraph;
import org.commonmark.node.Text;
import org.commonmark.parser.Parser;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.neighbor.Walker;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.ValidationEvent;

import java.util.ArrayList;
import java.util.List;

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
        for (Shape localService : model.getShapesWithTrait(LocalServiceTrait.class)) {
            for (Shape shape : new Walker(model).walkShapes(localService)) {
                var trait = shape.getTrait(DocumentationTrait.class);
                if (trait.isPresent()) {
                    Node document = parser.parse(trait.get().getValue());
                    if (!isDocumentWithNoMarkup(document)) {
                        events.add(danger(shape,
                                "smithy-dafny currently only supports @documentation with plaintext content, but this shape's documentation contains markdown."
                        ));
                    }
                }
            }
        }
        return events;
    }

    public static boolean isDocumentWithNoMarkup(Node document) {
        if (!(document instanceof Document)) {
            return false;
        }

        Node next;
        for(Node paragraph = document.getFirstChild(); paragraph != null; paragraph = next) {
            next = paragraph.getNext();

            if (!(paragraph instanceof Paragraph)) {
                return false;
            }
            var text = getOnlyChild(paragraph);
            if (!(text instanceof Text)) {
                return false;
            }
        }

        return true;
    }

    private static Node getOnlyChild(Node node) {
        var child = node.getFirstChild();
        if (child == null || child != node.getLastChild()) {
            return null;
        }
        return child;
    }
}
