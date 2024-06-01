// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.TypeName;
import org.junit.Before;
import org.junit.Test;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class AwsSdkNativeTest {

  AwsSdkNativeV1 underTest;

  @Before
  public void setup() {
    underTest = setupLocalModel(ModelConstants.MOCK_KMS, "kms");
  }

  @Test
  public void testIsInServiceNameSpaceSimple() {
    assertTrue(
      underTest.isInServiceNameSpace(
        ShapeId.fromParts("com.amazonaws.kms", "DoSomething")
      )
    );
  }

  @Test
  public void testIsInServiceNameSpaceOneDeep() {
    assertTrue(
      underTest.isInServiceNameSpace(
        ShapeId.fromParts("com.amazonaws.kms.model", "DoSomething")
      )
    );
  }

  @Test
  public void testIsInServiceNameSpaceNegative() {
    assertFalse(
      underTest.isInServiceNameSpace(
        ShapeId.fromParts("com.amazonaws.alice", "bob")
      )
    );
  }

  @Test
  public void testTypeForStructure() {
    final TypeName expected = ClassName.bestGuess(
      "com.amazonaws.services.kms.model.DoSomethingRequest"
    );
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("com.amazonaws.kms", "DoSomethingRequest")
    );
    assertEquals(expected, actual);
  }

  @Test
  public void testTypeForServiceKMS() {
    final TypeName expected = ClassName.bestGuess(
      "com.amazonaws.services.kms.AWSKMS"
    );
    final TypeName actual = underTest.typeForShape(
      ShapeId.fromParts("com.amazonaws.kms", "KeyManagementService")
    );
    assertEquals(expected, actual);
  }

  @Test
  public void testBaseErrorForServiceKMS() {
    final TypeName expected = ClassName.bestGuess(
      "com.amazonaws.services.kms.model.AWSKMSException"
    );
    final TypeName actual = underTest.baseErrorForService();
    assertEquals(expected, actual);
  }

  @Test
  public void checkForAwsServiceConstants() {
    Model localModel = TestModel.setupModel((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        ModelConstants.OTHER_NAMESPACE
      )
    );
    ServiceShape serviceShape = ModelUtils.serviceFromNamespace(
      localModel,
      AwsSdkNameResolverHelpers.namespaceForService("other")
    );
    assertThrows(
      IllegalArgumentException.class,
      () -> new AwsSdkNativeV1(serviceShape, localModel)
    );
  }

  static AwsSdkNativeV1 setupLocalModel(
    String rawModel,
    String awsServiceName
  ) {
    Model localModel = TestModel.setupModel((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel("test.smithy", rawModel)
    );
    ServiceShape serviceShape = ModelUtils.serviceFromNamespace(
      localModel,
      AwsSdkNameResolverHelpers.namespaceForService(awsServiceName)
    );
    return new AwsSdkNativeV1(serviceShape, localModel);
  }
}
