// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import java.util.Arrays;
import java.util.Collection;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.ForEachDafnyTest;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

public class DafnyTest extends ForEachDafnyTest {

  Dafny underTest;
  protected Model model;

  public DafnyTest(DafnyVersion dafnyVersion) {
    String rawModel =
      """
      namespace smithy.example
      service Example {}
      resource MyResource {}
      list MyList { member: String }
      map MyMap { key: String, value: String }
      structure MyStructure {}
      """;
    model =
      TestModel.setupModel((builder, modelAssembler) ->
        modelAssembler.addUnparsedModel("test.smithy", rawModel)
      );
    ServiceShape serviceShape = ModelUtils.serviceFromNamespace(
      model,
      "smithy.example"
    );
    underTest =
      new Dafny(
        "Dafny.Smithy.Example",
        model,
        serviceShape,
        CodegenSubject.AwsSdkVersion.V2,
        dafnyVersion
      );
  }

  @Test
  public void packageName() {
    final String expected = "Dafny.Smithy.Example";
    final String actual = underTest.packageName();
    assertEquals(expected, actual);
  }

  @Test
  public void typeForShapeBlob() {
    final String expected = "dafny.DafnySequence<? extends java.lang.Byte>";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.api", "Blob")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeBoolean() {
    final String expected = "java.lang.Boolean";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.api", "Boolean")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeString() {
    final String expected =
      "dafny.DafnySequence<? extends java.lang.Character>";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.api", "String")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeInteger() {
    final String expected = "java.lang.Integer";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.api", "Integer")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeTimestamp() {
    final String expected =
      "dafny.DafnySequence<? extends java.lang.Character>";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.api", "Timestamp")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeListOfStrings() {
    final String expected =
      "dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Character>>";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.example", "MyList")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeMapKeyStringValueString() {
    final String expected =
      "dafny.DafnyMap<" +
      "? extends dafny.DafnySequence<? extends java.lang.Character>, " +
      "? extends dafny.DafnySequence<? extends java.lang.Character>" +
      ">";
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.example", "MyMap")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public void getMemberField() {
    Model localModel = TestSetupUtils.setupTwoLocalModel(
      ModelConstants.KMS_KITCHEN,
      ModelConstants.OTHER_NAMESPACE
    );
    ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
    StructureShape structureShape = localModel.expectShape(
      structureId,
      StructureShape.class
    );
    MemberShape stringMember = structureShape.getMember("name").get();
    CodeBlock actual = Dafny.getMemberField(stringMember);
    String expected = "dtor_name()";
    tokenizeAndAssertEqual(expected, actual.toString());
  }

  @Test
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public void getMemberFieldValue() {
    Model localModel = TestSetupUtils.setupTwoLocalModel(
      ModelConstants.KMS_KITCHEN,
      ModelConstants.OTHER_NAMESPACE
    );
    ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
    StructureShape structureShape = localModel.expectShape(
      structureId,
      StructureShape.class
    );
    // if required, get via Field
    MemberShape requiredMember = structureShape.getMember("name").get();
    CodeBlock actualRequired = Dafny.getMemberFieldValue(requiredMember);
    String expectedRequired = "dtor_name()";
    tokenizeAndAssertEqual(expectedRequired, actualRequired.toString());
    // if optional, get via dtor_value()
    MemberShape optionalField = structureShape.getMember("message").get();
    CodeBlock actualOptional = Dafny.getMemberFieldValue(optionalField);
    String expectedOptional = "dtor_message().dtor_value()";
    tokenizeAndAssertEqual(expectedOptional, actualOptional.toString());
  }

  @Test
  public void typeForShapeMember() {}

  @Test
  public void typeForShapeStructure() {
    final String expected = "smithy.example.internaldafny.types.MyStructure";
    TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.example", "MyStructure")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeService() {
    final String expected = "smithy.example.internaldafny.types.IExampleClient";
    TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.example", "Example")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }

  @Test
  public void typeForShapeResource() {
    final String expected = "smithy.example.internaldafny.types.IMyResource";
    TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("smithy.example", "MyResource")
    );
    final String actualString = actual.toString();
    assertEquals(expected, actualString);
  }
}
