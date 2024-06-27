package software.amazon.polymorph.traits;

import org.commonmark.node.Document;
import org.commonmark.node.Node;
import org.commonmark.node.Paragraph;
import org.commonmark.node.Text;
import org.commonmark.parser.Parser;
import software.amazon.smithy.model.Model;
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
        for (Shape shape : model.getShapesWithTrait(DocumentationTrait.class)) {
            DocumentationTrait trait = shape.expectTrait(DocumentationTrait.class);

            Parser parser = Parser.builder().build();
            Node document = parser.parse(trait.getValue());
            if (!isDocumentWithNoMarkup(document)) {
                events.add(danger(shape,
            "smithy-dafny currently only supports @documentation with plaintext content, but this shape's documentation contains markdown."
                ));
            }
        }
        return events;
    }

    public static boolean isDocumentWithNoMarkup(Node document) {
        if (!(document instanceof Document)) {
            return false;
        }
        var paragraph = getOnlyChild(document);
        if (!(paragraph instanceof Paragraph)) {
            return false;
        }
        var text = getOnlyChild(paragraph);
        if (!(text instanceof Text)) {
            return false;
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
