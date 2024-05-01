// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.polymorph.smithydafny.DafnyNameResolver.traitNameForServiceClient;

import com.squareup.javapoet.ClassName;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.StringUtils;

public class AwsSdkDafnyV1 extends Dafny {

  public AwsSdkDafnyV1(
    ServiceShape serviceShape,
    Model model,
    DafnyVersion dafnyVersion
  ) {
    super(
      packageNameForServiceShape(serviceShape),
      model,
      serviceShape,
      CodegenSubject.AwsSdkVersion.V1,
      dafnyVersion
    );
  }

  @Override
  ClassName classNameForService(ServiceShape shape) {
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return classNameForAwsService(shape);
    }
    return super.classNameForService(shape);
  }

  public static ClassName classNameForAwsService(ServiceShape shape) {
    return ClassName.get(
      modelPackageNameForNamespace(shape.getId().getNamespace()),
      DafnyNameResolverHelpers.dafnyCompilesExtra_(
        traitNameForServiceClient(shape)
      )
    );
  }

  @Override
  ClassName classNameForResource(ResourceShape shape) {
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return classNameForAwsResource(shape);
    }
    return super.classNameForResource(shape);
  }

  public static ClassName classNameForAwsResource(ResourceShape shape) {
    return ClassName.get(
      modelPackageNameForNamespace(shape.getId().getNamespace()),
      DafnyNameResolverHelpers.dafnyCompilesExtra_(
        "I%s".formatted(StringUtils.capitalize(shape.getId().getName()))
      )
    );
  }
}
