// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk;

import static software.amazon.polymorph.utils.AwsSdkNameResolverHelpers.namespaceForService;
import static software.amazon.polymorph.utils.ModelUtils.serviceFromNamespace;

import java.util.function.BiConsumer;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.awssdk.v1.JavaAwsSdkV1;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.JavaAwsSdkV2;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;

public class TestSetupUtils {

  public static Model setupLocalModel(String rawModel) {
    BiConsumer<ServiceShape.Builder, ModelAssembler> updater;
    updater =
      ((builder, modelAssembler) ->
          modelAssembler.addUnparsedModel("test.smithy", rawModel));
    return TestModel.setupModel(updater);
  }

  public static Model setupTwoLocalModel(
    String rawModelOne,
    String rawModelTwo
  ) {
    BiConsumer<ServiceShape.Builder, ModelAssembler> updater;
    updater =
      ((builder, modelAssembler) ->
          modelAssembler
            .addUnparsedModel("testOne.smithy", rawModelOne)
            .addUnparsedModel("testTwo.smithy", rawModelTwo));
    return TestModel.setupModel(updater);
  }

  public static JavaAwsSdkV1 setupAwsSdkV1(Model localModel, String awsName) {
    ServiceShape serviceShape = serviceFromNamespace(
      localModel,
      namespaceForService(awsName)
    );
    return JavaAwsSdkV1.createJavaAwsSdkV1(serviceShape, localModel);
  }

  public static JavaAwsSdkV2 setupAwsSdkV2(
    Model localModel,
    String awsName,
    DafnyVersion dafnyVersion
  ) {
    ServiceShape serviceShape = serviceFromNamespace(
      localModel,
      namespaceForService(awsName)
    );
    return JavaAwsSdkV2.createJavaAwsSdkV2(
      serviceShape,
      localModel,
      dafnyVersion
    );
  }

  public static JavaLibrary setupLibrary(
    Model localModel,
    String namespace,
    DafnyVersion dafnyVersion
  ) {
    ServiceShape serviceShape = serviceFromNamespace(localModel, namespace);
    return new JavaLibrary(
      localModel,
      serviceShape,
      CodegenSubject.AwsSdkVersion.V1,
      dafnyVersion
    );
  }
}
