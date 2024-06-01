// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

import java.util.EnumSet;
import java.util.function.BiConsumer;
import org.junit.Assert;
import org.junit.Test;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.SourceLocation;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.EnumShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public class DotNetNameResolverTest {

  private DotNetNameResolver setupNameResolver(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel(updater);
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new DotNetNameResolver(model, serviceShape);
  }

  @Test
  public void testEncodeShapeIdRoot() {
    final ShapeId shapeId = ShapeId.fromParts("com.foo.bar_baz", "ShapeName");
    final String encodedShapeId = DotNetNameResolver.encodedIdentForShapeId(
      shapeId
    );
    Assert.assertEquals(
      encodedShapeId,
      "N3_com__N3_foo__N7_bar_baz__S9_ShapeName"
    );
  }

  @Test
  public void testEncodeShapeIdWithMember() {
    final ShapeId shapeId = ShapeId.fromParts(
      "com.foo.bar_baz",
      "ShapeName",
      "MemberName"
    );
    final String encodedShapeId = DotNetNameResolver.encodedIdentForShapeId(
      shapeId
    );
    Assert.assertEquals(
      encodedShapeId,
      "N3_com__N3_foo__N7_bar_baz__S9_ShapeName__M10_MemberName"
    );
  }

  @Test
  public void testEncodeShapeIdWithSuspiciousIdents() {
    final ShapeId shapeId = ShapeId.fromParts(
      "N3_com__.__bar_baz.M10_MemberName",
      "N3_foo",
      "__SUS__S1__"
    );
    final String encodedShapeId = DotNetNameResolver.encodedIdentForShapeId(
      shapeId
    );
    Assert.assertEquals(
      encodedShapeId,
      "N8_N3_com____N9___bar_baz__N14_M10_MemberName__S6_N3_foo__M11___SUS__S1__"
    );
  }

  @Test
  public void testTypeConverterForShape() {
    final StructureShape foobarStructureShape =
      TestModel.setupFoobarStructureShape();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(foobarStructureShape)
    );

    final String toDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(
        foobarStructureShape.getId(),
        TypeConversionDirection.TO_DAFNY
      );
    Assert.assertEquals(
      "ToDafny_N4_test__N6_foobar__S6_Foobar",
      toDafnyConverterName
    );

    final String fromDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(
        foobarStructureShape.getId(),
        TypeConversionDirection.FROM_DAFNY
      );
    Assert.assertEquals(
      "FromDafny_N4_test__N6_foobar__S6_Foobar",
      fromDafnyConverterName
    );
  }

  @Test
  public void testDafnyNamespaceForShapeId() {
    final ShapeId shapeId = ShapeId.fromParts("test.fooBar.baz", "Whatever");
    final String dafnyNamespace =
      DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(shapeId);
    Assert.assertEquals("test.foobar.baz.internaldafny.types", dafnyNamespace);
  }

  @Test
  public void testDafnyTypeForSimpleShapes() {
    final DotNetNameResolver nameResolver = setupNameResolver(
      (_builder, _modelAssembler) -> {}
    );
    assertEquals(
      "Dafny.ISequence<byte>",
      nameResolver.dafnyTypeForShape(ShapeId.from("smithy.api#Blob"))
    );
    assertEquals(
      "bool",
      nameResolver.dafnyTypeForShape(ShapeId.from("smithy.api#Boolean"))
    );
    assertEquals(
      "Dafny.ISequence<char>",
      nameResolver.dafnyTypeForShape(ShapeId.from("smithy.api#String"))
    );
    assertEquals(
      "int",
      nameResolver.dafnyTypeForShape(ShapeId.from("smithy.api#Integer"))
    );
    assertEquals(
      "long",
      nameResolver.dafnyTypeForShape(ShapeId.from("smithy.api#Long"))
    );
  }

  @Test
  public void testDafnyTypeForEnum() {
    final EnumTrait enumTrait = EnumTrait
      .builder()
      .addEnum(EnumDefinition.builder().value("value").build())
      .build();
    final StringShape enumStringShape = StringShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "EnumString"))
      .addTrait(enumTrait)
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(enumStringShape)
    );
    assertEquals(
      "test.foobar.internaldafny.types._IEnumString",
      nameResolver.dafnyTypeForShape(enumStringShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForEnumV2() {
    final MemberShape memberShape = MemberShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "EnumShape", "FOO"))
      .target(UnitTypeTrait.UNIT)
      .build();
    final EnumShape enumShape = EnumShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "EnumShape"))
      .addMember(memberShape)
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(enumShape)
    );
    assertEquals(
      "test.foobar.internaldafny.types._IEnumShape",
      nameResolver.dafnyTypeForShape(enumShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForUtf8Bytes() {
    final StringShape stringShape = StringShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Utf8BytesString"))
      .addTrait(new DafnyUtf8BytesTrait())
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(stringShape)
    );
    assertEquals(
      "Dafny.ISequence<byte>",
      nameResolver.dafnyTypeForShape(stringShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForAggregateTypes() {
    final ShapeId listShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "BoolList"
    );
    final ListShape listShape = ListShape
      .builder()
      .id(listShapeId)
      .member(ShapeId.from("smithy.api#Boolean"))
      .build();
    final MapShape mapShape = MapShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "StringToBoolListMap"))
      .key(ShapeId.from("smithy.api#String"))
      .value(listShapeId)
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
      ((builder, modelAssembler) -> {
          modelAssembler.addShape(listShape);
          modelAssembler.addShape(mapShape);
        })
    );
    assertEquals(
      "Dafny.ISequence<bool>",
      nameResolver.dafnyTypeForShape(listShape.getId())
    );
    assertEquals(
      "Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<bool>>",
      nameResolver.dafnyTypeForShape(mapShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForStructure() {
    final StructureShape foobarStructureShape =
      TestModel.setupFoobarStructureShape();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(foobarStructureShape)
    );
    assertEquals(
      "test.foobar.internaldafny.types._IFoobar",
      nameResolver.dafnyTypeForShape(foobarStructureShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForResourceReferenceStructure() {
    final ShapeId resourceShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "TestResource"
    );
    final ResourceShape resourceShape = ResourceShape
      .builder()
      .id(resourceShapeId)
      .build();

    final ReferenceTrait referenceTrait = ReferenceTrait
      .builder()
      .referentType(ReferenceTrait.ReferentType.RESOURCE)
      .referentId(resourceShapeId)
      .build();
    final StructureShape referenceShape = StructureShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "ResourceReference"))
      .addTrait(referenceTrait)
      .build();

    final DotNetNameResolver nameResolver = setupNameResolver(
      (builder, modelAssembler) -> {
        modelAssembler.addShape(referenceShape);
        modelAssembler.addShape(resourceShape);
      }
    );
    assertEquals(
      "test.foobar.internaldafny.types.ITestResource",
      nameResolver.dafnyTypeForShape(referenceShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForPositionalStructure() {
    final PositionalTrait positionalTrait = PositionalTrait.builder().build();
    final StructureShape positionalShape = StructureShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "PositionalShape"))
      .addMember("aBoolean", ShapeId.from("smithy.api#Boolean"))
      .addTrait(positionalTrait)
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(positionalShape)
    );
    assertEquals(
      "bool",
      nameResolver.dafnyTypeForShape(positionalShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForErrorStructure() {
    final ErrorTrait errorTrait = new ErrorTrait(
      "client",
      new SourceLocation("test.smithy")
    );
    final StructureShape errorShape = StructureShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "ErrorShape"))
      .addMember("message", ShapeId.from("smithy.api#String"))
      .addTrait(errorTrait)
      .build();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(errorShape)
    );
    assertEquals(
      "test.foobar.internaldafny.types.Error_ErrorShape",
      nameResolver.dafnyTypeForShape(errorShape.getId())
    );
  }

  @Test
  public void testDafnyTypeForMember() {
    final StructureShape foobarStructureShape =
      TestModel.setupFoobarStructureShape();
    final DotNetNameResolver nameResolver = setupNameResolver(
        (builder, modelAssembler) ->
      modelAssembler.addShape(foobarStructureShape)
    );
    assertEquals(
      "Wrappers_Compile._IOption<int>",
      nameResolver.dafnyTypeForShape(
        ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar", "someInt")
      )
    );
    assertEquals(
      "Wrappers_Compile._IOption<Dafny.ISequence<char>>",
      nameResolver.dafnyTypeForShape(
        ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar", "someString")
      )
    );
    assertEquals(
      "bool",
      nameResolver.dafnyTypeForShape(
        ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar", "someBool")
      )
    );
  }

  @Test
  public void testDafnyImplForServiceClient() {
    final DotNetNameResolver nameResolver = setupNameResolver(
      (_builder, _modelAssembler) -> {}
    );
    final String actualName = nameResolver.dafnyImplForServiceClient();
    final String expectedName =
      "test.foobar.internaldafny.__default.FoobarServiceFactory";
    Assert.assertEquals(expectedName, actualName);
  }

  @Test
  public void testCapitalizeNamespaceSegment() {
    assertEquals(
      "FooBar",
      DotNetNameResolver.capitalizeNamespaceSegment("fooBar")
    );
    assertEquals(
      "EncryptionSDK",
      DotNetNameResolver.capitalizeNamespaceSegment("encryptionSdk")
    );
    assertEquals(
      "KMSKeyring",
      DotNetNameResolver.capitalizeNamespaceSegment("KmsKeyring")
    );
    assertEquals(
      "RSAOaepSha512Mgf1",
      DotNetNameResolver.capitalizeNamespaceSegment("rsaOaepSha512Mgf1")
    );
    assertEquals(
      "ALLCAPS",
      DotNetNameResolver.capitalizeNamespaceSegment("ALLCAPS")
    );

    // all together now
    assertEquals(
      "AWSKMSSDKAESRSA",
      DotNetNameResolver.capitalizeNamespaceSegment("awsKmsSdkAesRsa")
    );
  }

  @Test
  public void testCapitalizeNamespaceSegmentFailsOnInvalidSegment() {
    Assert.assertThrows(
      IllegalArgumentException.class,
      () -> DotNetNameResolver.capitalizeNamespaceSegment("sausage-case")
    );
    // snake_Case is valid for smithy
  }
}
