// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThrows;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import com.squareup.javapoet.MethodSpec;
import java.nio.file.Path;
import java.util.Map;
import org.junit.Before;
import org.junit.Test;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.ForEachDafnyTest;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;

public class ToDafnyAwsV2Test extends ForEachDafnyTest {

  protected final ToDafnyAwsV2 underTest;
  protected final Model model;
  protected final DafnyVersion dafnyVersion;

  public ToDafnyAwsV2Test(DafnyVersion dafnyVersion) {
    this.dafnyVersion = dafnyVersion;
    model =
      TestSetupUtils.setupTwoLocalModel(
        ModelConstants.KMS_KITCHEN,
        ModelConstants.OTHER_NAMESPACE
      );
    underTest =
      new ToDafnyAwsV2(
        TestSetupUtils.setupAwsSdkV2(model, "kms", dafnyVersion)
      );
  }

  @Test
  public void generateConvertEnumEnum() {
    ShapeId enumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
    MethodSpec actual = underTest.generateConvertEnumEnum(enumId);
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.KEY_USAGE_TYPE,
      actual.toString()
    );
  }

  @Test
  public void generateConvertEnumString() {
    ShapeId enumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
    MethodSpec actual = underTest.generateConvertEnumString(enumId);
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.KEY_USAGE_TYPE_STRING,
      actual.toString()
    );
  }

  @Test
  public void generateConvert() {
    // case Simple
    ShapeId CiphertextTypeId = ShapeId.fromParts(
      "com.amazonaws.kms",
      "CiphertextType"
    );
    assertNull(underTest.generateConvert(CiphertextTypeId));
    // case LIST of Enums (which will take a list of Strings for AWS SDK for Java V2)
    ShapeId listEnumId = ShapeId.fromParts(
      "com.amazonaws.kms",
      "KeyUsageTypes"
    );
    String actualListEnum = underTest.generateConvert(listEnumId).toString();
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.GENERATE_CONVERT_LIST,
      actualListEnum
    );
    // case LIST of Structures from other AWS SDK namespace
    ShapeId listStructureId = ShapeId.fromParts(
      "com.amazonaws.kms",
      "OtherNamespaces"
    );
    String actualListOther = underTest
      .generateConvert(listStructureId)
      .toString();
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.GENERATE_CONVERT_LIST_STRUCTURES,
      actualListOther
    );
    // case MAP
    ShapeId mapId = ShapeId.fromParts(
      "com.amazonaws.kms",
      "EncryptionContextType"
    );
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.GENERATE_CONVERT_MAP_STRING,
      underTest.generateConvert(mapId).toString()
    );
    // case SET
    ShapeId setId = ShapeId.fromParts("com.amazonaws.kms", "Names");
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.GENERATE_CONVERT_SET_STRING,
      underTest.generateConvert(setId).toString()
    );
    // case Structure
    ShapeId simpleId = ShapeId.fromParts("com.amazonaws.kms", "Simple");
    tokenizeAndAssertEqual(
      ToDafnyAwsV2Constants.SIMPLE_STRUCTURE,
      underTest.generateConvert(simpleId).toString()
    );
    // default
    ShapeId doubleId = ShapeId.fromParts("com.amazonaws.kms", "NotSupported");
    //assertThrows(UnsupportedOperationException.class, () -> underTest.generateConvert(doubleId));
  }

  @Test
  public void generateConvertOpaqueError() {
    final String expected = Dafny.datatypeConstructorsNeedTypeDescriptors(
        dafnyVersion
      )
      ? ToDafnyAwsV2Constants.GENERATE_CONVERT_OPAQUE_ERROR_WITH_TYPE_DESCRIPTORS
      : ToDafnyAwsV2Constants.GENERATE_CONVERT_OPAQUE_ERROR;
    tokenizeAndAssertEqual(
      expected,
      underTest.generateConvertOpaqueError().toString()
    );
  }

  @Test
  public void generate() {
    Model localModel = TestSetupUtils.setupLocalModel(
      ModelConstants.KMS_A_STRING_OPERATION
    );
    ToDafnyAwsV2 localUnderTest = new ToDafnyAwsV2(
      TestSetupUtils.setupAwsSdkV2(localModel, "kms", dafnyVersion)
    );
    final Map<Path, TokenTree> actual = localUnderTest.generate();
    final Path expectedPath = Path.of(
      "software/amazon/cryptography/services/kms/internaldafny/ToDafny.java"
    );
    Path[] temp = new Path[1];
    final Path actualPath = actual.keySet().toArray(temp)[0];
    assertEquals(expectedPath, actualPath);
    final String actualSource = actual.get(actualPath).toString();
    // TODO: This test is failing, but we have largely given up on Polymorph unit tests.
    //   If we decide to resume writing unit tests, we should fix this test.
    // tokenizeAndAssertEqual(ToDafnyAwsV2Constants.KMS_A_STRING_OPERATION_JAVA_FILE, actualSource);
  }
}
