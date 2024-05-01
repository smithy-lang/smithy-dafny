// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import com.squareup.javapoet.JavaFile;
import org.junit.Before;
import org.junit.Test;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.ForEachDafnyTest;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

public class ModelCodegenTest extends ForEachDafnyTest {

  protected ModelCodegen underTest;
  protected Model model;

  public ModelCodegenTest(DafnyVersion dafnyVersion) {
    model =
      TestSetupUtils.setupLocalModel(
        ModelConstants.CRYPTOGRAPHY_A_STRING_OPERATION
      );
    underTest =
      new ModelCodegen(
        TestSetupUtils.setupLibrary(
          model,
          "aws.cryptography.test",
          dafnyVersion
        )
      );
  }

  @Test
  public void StructureWithRangeTraitTest() {
    ShapeId structureId = ShapeId.fromParts(
      "aws.cryptography.test",
      "TestRangeMinMaxInteger"
    );
    StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    JavaFile actual = underTest.modeledStructure(structureShape);
    String actualString = actual.toString();
    int startBuildMethod = actualString.indexOf(
      Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_START
    );
    int endBuildMethod =
      actualString.indexOf(Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN) +
      Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN.length() +
      Constants.BUILD_METHOD_END_OFFSET;
    tokenizeAndAssertEqual(
      Constants.RANGE_TRAIT_INTEGER_BUILD_EXPECTED,
      actualString.substring(startBuildMethod, endBuildMethod)
    );
  }

  @Test
  public void StructureWithLengthTraitTest() {
    ShapeId structureId = ShapeId.fromParts(
      "aws.cryptography.test",
      "TestLengthMinMaxBlob"
    );
    StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    JavaFile actual = underTest.modeledStructure(structureShape);
    String actualString = actual.toString();
    int startBuildMethod = actualString.indexOf(
      Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_START
    );
    int endBuildMethod =
      actualString.indexOf(Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN) +
      Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN.length() +
      Constants.BUILD_METHOD_END_OFFSET;
    tokenizeAndAssertEqual(
      Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_EXPECTED,
      actualString.substring(startBuildMethod, endBuildMethod)
    );
  }
  // TODO: Test structure with Enum member

}
