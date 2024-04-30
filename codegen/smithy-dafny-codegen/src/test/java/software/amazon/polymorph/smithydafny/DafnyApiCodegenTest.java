// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

import java.nio.file.Path;
import java.util.List;
import java.util.function.BiConsumer;
import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

// TODO: use Dafny tokenizer instead of C# tokenizer
public class DafnyApiCodegenTest {

  private static DafnyApiCodegen setupCodegen(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel(updater);
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new DafnyApiCodegen(
      model,
      serviceShape,
      Path.of(""),
      Path.of(""),
      new Path[0],
      false
    );
  }

  @Test
  public void testGenerateBlobTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @length(min: 1, max: 1024)
        blob SomeBlob
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateBlobTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeBlob")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeBlob = x: seq<uint8> | IsValid_SomeBlob(x) witness *
      predicate method IsValid_SomeBlob(x: seq<uint8>) { (1 <= |x| <= 1024) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateBoolTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        boolean SomeBool
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateBoolTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeBool")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      "type SomeBool = bool"
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateStringTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @length(min: 1, max: 1024)
        string SomeString
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateStringTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeString")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeString = x: string | IsValid_SomeString(x) witness *
      predicate method IsValid_SomeString(x: string) { (1 <= |x| <= 1024) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateEnumTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @enum([
            {value: "V1", name: "N1"},
            {value: "V2", name: "N2"},
            {value: "V3", name: "N3"},
        ])
        string SomeEnum
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateEnumTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeEnum")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      "datatype SomeEnum = | N1 | N2 | N3"
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateNumericTypeDefinitionInt() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @range(min: 1, max: 10)
        integer SomeInt
        """.formatted(SERVICE_NAMESPACE)
      )
    );

    final String actualCode = codegen
      .generateNumericTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeInt")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeInt = x: int32 | IsValid_SomeInt(x) witness *
      predicate method IsValid_SomeInt(x: int32) { (1 <= x <= 10) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateNumericTypeDefinitionLong() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @range(min: 1, max: 10)
        long SomeLong
        """.formatted(SERVICE_NAMESPACE)
      )
    );

    final String actualCode = codegen
      .generateNumericTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeLong")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeLong = x: int64 | IsValid_SomeLong(x) witness *
      predicate method IsValid_SomeLong(x: int64) { (1 <= x <= 10) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateListTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @length(min: 1, max: 10)
        list SomeList {
            member: Boolean
        }
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateListTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeList")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeList = x: seq<bool> | IsValid_SomeList(x) witness *
      predicate method IsValid_SomeList(x: seq<bool>) { (1 <= |x| <= 10) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateMapTypeDefinition() {
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        @length(min: 1, max: 10)
        map SomeMap {
            key: String,
            value: Boolean,
        }
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final String actualCode = codegen
      .generateMapTypeDefinition(
        ShapeId.fromParts(SERVICE_NAMESPACE, "SomeMap")
      )
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      type SomeMap = x: map<string, bool> | IsValid_SomeMap(x) witness *
      predicate method IsValid_SomeMap(x: map<string, bool>) { (1 <= |x| <= 10) }
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateStructureTypeDefinition() {
    final StructureShape foobarStructureShape =
      TestModel.setupFoobarStructureShape();
    final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addShape(foobarStructureShape)
    );

    final String actualCode = codegen
      .generateStructureTypeDefinition(foobarStructureShape.getId())
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      datatype Foobar = | Foobar(
         nameonly someInt: Option<int32> := Option.None,
         nameonly someString: Option<string> := Option.None,
         nameonly someBool: bool
      )
      """
    );
    assertEquals(expectedTokens, actualTokens);
  }
}
