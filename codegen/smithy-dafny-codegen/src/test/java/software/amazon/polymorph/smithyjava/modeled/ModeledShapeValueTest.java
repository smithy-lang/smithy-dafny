// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithyjava.modeled;

import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import com.squareup.javapoet.CodeBlock;
import java.net.URL;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import org.junit.Test;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.ForEachDafnyTest;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.validation.NodeValidationVisitor;
import software.amazon.smithy.model.validation.ValidatedResultException;
import software.amazon.smithy.model.validation.ValidationEvent;
import software.amazon.smithy.model.validation.node.TimestampValidationStrategy;

public class ModeledShapeValueTest extends ForEachDafnyTest {

  private final JavaLibrary underTest;

  private static Map<String, String> EXPECTED_VALUES = new HashMap<>();

  static {
    EXPECTED_VALUES.put(
      "NoParameters",
      """
      software.amazon.polymorph.model.MyNestedStructure.builder()
      .build()
      """
    );
    EXPECTED_VALUES.put(
      "StressTest",
      """
      software.amazon.polymorph.model.MyNestedStructure.builder()
          .myLong(123456789012345)
          .myInteger(42)
          .myBlob(java.nio.ByteBuffer.wrap("0101".getBytes(java.nio.charset.StandardCharsets.US_ASCII)))
          .myBoolean(false)
          .myList(java.util.Arrays.asList("1", "2", "3"))
          .myNestedList(java.util.Arrays.asList(new java.util.HashMap<String, software.amazon.polymorph.model.MyStructure>() {{
              put("a", software.amazon.polymorph.model.MyStructure.builder()
                              .c(java.util.Arrays.asList("b"))
                              .build());
          }}))
          .myStringMap(new java.util.HashMap<String, java.lang.String>() {{
              put("a", "b");
              put("c", "d");
          }})
          .myNestedMap(new java.util.HashMap<String, software.amazon.polymorph.model.MyStructure>() {{
              put("a", software.amazon.polymorph.model.MyStructure.builder()
                          .build());
              put("c", software.amazon.polymorph.model.MyStructure.builder()
                          .a(0)
                          .build());
          }})
          .build()
      """
    );
  }

  public ModeledShapeValueTest(DafnyVersion dafnyVersion) {
    final URL modelUrl = Objects.requireNonNull(
      this.getClass().getClassLoader().getResource("shapeValues.smithy")
    );
    final ModelAssembler assembler = new ModelAssembler();
    ModelUtils.addCustomTraitsToModelAssembler(assembler);
    final Model model = assembler.addImport(modelUrl).assemble().unwrap();
    underTest =
      TestSetupUtils.setupLibrary(model, "aws.polymorph", dafnyVersion);
  }

  @Test
  public void shapeValueTests() {
    ArrayNode testCases = (ArrayNode) underTest.model
      .getMetadata()
      .get("testCases");
    testCases.forEach(this::assertTestCaseCorrect);
  }

  public void assertTestCaseCorrect(Node testCase) {
    ObjectNode testCaseNode = (ObjectNode) testCase;
    String testId = testCaseNode.expectStringMember("id").getValue();
    ShapeId shapeId = ShapeId.from(
      testCaseNode.expectStringMember("shape").getValue()
    );
    Shape shape = underTest.model.expectShape(shapeId);
    Node value = testCaseNode.expectMember("value");

    // First check that the test case is valid.
    // This would normally already be done by various trait validators,
    // but not here since we're just using raw metadata to define test cases.
    validateTestCase(underTest.model, testId, shape, value);

    CodeBlock actual = ModeledShapeValue.shapeValue(
      underTest,
      false,
      shape,
      value
    );
    String expected = EXPECTED_VALUES.get(testId);
    tokenizeAndAssertEqual(expected, actual.toString());
  }

  private void validateTestCase(
    Model model,
    String id,
    Shape shape,
    Node node
  ) {
    NodeValidationVisitor visitor = NodeValidationVisitor
      .builder()
      .model(model)
      .eventShapeId(shape.getId())
      .value(node)
      .eventId("DummyValidatorName")
      .startingContext("metadata.testCases." + id)
      .timestampValidationStrategy(TimestampValidationStrategy.EPOCH_SECONDS)
      .addFeature(NodeValidationVisitor.Feature.ALLOW_CONSTRAINT_ERRORS)
      .build();
    List<ValidationEvent> events = shape.accept(visitor);
    if (!events.isEmpty()) {
      throw new ValidatedResultException(events);
    }
  }
}
