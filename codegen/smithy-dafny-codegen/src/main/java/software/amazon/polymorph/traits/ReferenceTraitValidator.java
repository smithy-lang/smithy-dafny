package software.amazon.polymorph.traits;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.Severity;
import software.amazon.smithy.model.validation.ValidationEvent;
import software.amazon.smithy.smoketests.traits.SmokeTestCase;
import software.amazon.smithy.smoketests.traits.SmokeTestsTrait;

import java.util.ArrayList;
import java.util.List;

/**
 * Validates correct usage of the @references trait,
 * which is a type refinement trait and substantially changes
 * how the shape is used in the model.
 *
 * This is not yet complete, especially since there are existing
 * models out there misusing the trait.
 * For now, we're only validating that smokeTests.params values
 * never try to bind a node value to a reference shape,
 * since there's no way to express a reference as a literal node value.
 */
public class ReferenceTraitValidator extends AbstractValidator {

    @Override
    public List<ValidationEvent> validate(Model model) {
        OperationIndex operationIndex = OperationIndex.of(model);
        List<ValidationEvent> events = new ArrayList<>();
        for (Shape shape : model.getShapesWithTrait(SmokeTestsTrait.class)) {
            SmokeTestsTrait trait = shape.expectTrait(SmokeTestsTrait.class);
            List<SmokeTestCase> testCases = trait.getTestCases();

            for (SmokeTestCase testCase : testCases) {
                StructureShape input = operationIndex.expectInputShape(shape);
                if (input != null && testCase.getParams().isPresent()) {
                    // This is overly restrictive,
                    // since it's technically possible to just not provide a value
                    // for a non-@required reference.
                    // But it's simpler to just reject all references
                    // given it's unlikely anyone will want to use smokeTests
                    // on local services that use references.
                    Selector selector = Selector.parse(
                            "[id=" + input.getId() + "]\n" +
                                    ":is(*, ~> *)\n" +
                                    "[trait|aws.polymorph#reference]\n"
                    );
                    for (Shape matchingShape : selector.select(model)) {
                        events.add(ValidationEvent.builder()
                                .id(getName())
                                .severity(Severity.ERROR)
                                .sourceLocation(testCase.getParams().get().getSourceLocation())
                                .shapeId(matchingShape.toShapeId())
                                .message("smokeTests.params cannot be used for input structures that use the @references trait")
                                .build());
                    }
                }
            }
        }
        return events;
    }
}
