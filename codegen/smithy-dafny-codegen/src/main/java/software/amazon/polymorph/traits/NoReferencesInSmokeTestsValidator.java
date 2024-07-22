// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import java.util.ArrayList;
import java.util.List;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.ValidationEvent;
import software.amazon.smithy.smoketests.traits.SmokeTestCase;
import software.amazon.smithy.smoketests.traits.SmokeTestsTrait;

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
public class NoReferencesInSmokeTestsValidator extends AbstractValidator {

  @Override
  public List<ValidationEvent> validate(Model model) {
    OperationIndex operationIndex = OperationIndex.of(model);
    List<ValidationEvent> events = new ArrayList<>();
    for (Shape shape : model.getShapesWithTrait(SmokeTestsTrait.class)) {
      SmokeTestsTrait trait = shape.expectTrait(SmokeTestsTrait.class);

      // Generate a warning for any use of this trait,
      // just because we only support it to the extent that it is useful
      // for internal testing of things like constraints traits.
      events.add(
        warning(
          shape,
          "smithy.test#smokeTests is only intended for internal testing"
        )
      );

      for (SmokeTestCase testCase : trait.getTestCases()) {
        StructureShape input = operationIndex.expectInputShape(shape);
        if (input != null && testCase.getParams().isPresent()) {
          // This is overly restrictive,
          // since it's technically possible to just not provide a value
          // for a non-@required reference.
          // But it's simpler to just reject all references
          // given it's unlikely anyone will want to use smokeTests
          // on local services that use references.
          Selector selector = Selector.parse(
            "[id=" +
            input.getId() +
            "]\n" +
            ":is(*, ~> *)\n" +
            "[trait|aws.polymorph#reference]\n"
          );
          for (Shape matchingShape : selector.select(model)) {
            events.add(
              error(
                matchingShape,
                testCase.getParams().get(),
                "smokeTests.params cannot be used for input structures that use the @references trait"
              )
            );
          }
        }
      }
    }
    return events;
  }
}
