// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v1;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThrows;

import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;

public class ToDafnyAwsV1Test {

  protected ToDafnyAwsV1 underTest;
  protected Model model;
  /* @Before
    public void setup() {
        model = TestSetupUtils.setupTwoLocalModel(ModelConstants.KMS_KITCHEN, ModelConstants.OTHER_NAMESPACE);
        underTest  = new ToDafnyAwsV1(TestSetupUtils.setupAwsSdkV1(model, "kms"));
    }

    @Test
    public void generateConvertResponseV1() {
        Model localModel = TestSetupUtils.setupLocalModel(ModelConstants.KMS_A_STRING_OPERATION);
        ToDafnyAwsV1 localUnderTest = new ToDafnyAwsV1(TestSetupUtils.setupAwsSdkV1(localModel, "kms"));
        ShapeId responseId = ShapeId.fromParts("com.amazonaws.kms", "DoSomethingResponse");
        MethodSpec actual = localUnderTest.generateConvertResponseV1(responseId);
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.DO_SOMETHING_RESPONSE, actual.toString());
    }

    @Test
    public void generateConvertEnumEnum() {
        ShapeId enumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
        MethodSpec actual = underTest.generateConvertEnumEnum(enumId);
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.KEY_USAGE_TYPE, actual.toString());
    }

    @Test
    public void generateConvertEnumString() {
        ShapeId enumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
        MethodSpec actual = underTest.generateConvertEnumString(enumId);
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.KEY_USAGE_TYPE_STRING, actual.toString());
    }

    @Test
    public void generateConvert() {
        // case Simple
        ShapeId CiphertextTypeId = ShapeId.fromParts("com.amazonaws.kms", "CiphertextType");
        assertNull(underTest.generateConvert(CiphertextTypeId));
        // case LIST of Enums (which will take a list of Strings for AWS SDK for Java V1)
        ShapeId listEnumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageTypes");
        String actualListEnum = underTest.generateConvert(listEnumId).toString();
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.GENERATE_CONVERT_LIST, actualListEnum);
        // case LIST of Structures from other AWS SDK namespace
        ShapeId listStructureId = ShapeId.fromParts("com.amazonaws.kms", "OtherNamespaces");
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.GENERATE_CONVERT_LIST_STRUCTURES, underTest.generateConvert(listStructureId).toString());
        // case MAP
        ShapeId mapId = ShapeId.fromParts("com.amazonaws.kms", "EncryptionContextType");
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.GENERATE_CONVERT_MAP_STRING, underTest.generateConvert(mapId).toString());
        // case SET
        ShapeId setId = ShapeId.fromParts("com.amazonaws.kms", "Names");
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.GENERATE_CONVERT_SET_STRING, underTest.generateConvert(setId).toString());
        // case Structure
        ShapeId simpleId = ShapeId.fromParts("com.amazonaws.kms", "Simple");
        tokenizeAndAssertEqual(ToDafnyConstants.SIMPLE_STRUCTURE, underTest.generateConvert(simpleId).toString());
        // default
        ShapeId doubleId = ShapeId.fromParts("com.amazonaws.kms", "NotSupported");
        //assertThrows(UnsupportedOperationException.class, () -> underTest.generateConvert(doubleId));
    }

    @Test
    public void generateConvertOpaqueError() {
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.GENERATE_CONVERT_OPAQUE_ERROR, underTest.generateConvertOpaqueError().toString());
    }

    @Test
    public void generate() {
        Model localModel = TestSetupUtils.setupLocalModel(ModelConstants.KMS_A_STRING_OPERATION);
        ToDafnyAwsV1 localUnderTest = new ToDafnyAwsV1(TestSetupUtils.setupAwsSdkV1(localModel, "kms"));
        final Map<Path, TokenTree> actual = localUnderTest.generate();
        final Path expectedPath = Path.of("Dafny/Com/Amazonaws/Kms/ToDafny.java");
        Path[] temp = new Path[1];
        final Path actualPath = actual.keySet().toArray(temp)[0];
        assertEquals(expectedPath, actualPath);
        final String actualSource = actual.get(actualPath).toString();
        tokenizeAndAssertEqual(ToDafnyAwsV1Constants.KMS_A_STRING_OPERATION_JAVA_FILE, actualSource);
    }*/
}
