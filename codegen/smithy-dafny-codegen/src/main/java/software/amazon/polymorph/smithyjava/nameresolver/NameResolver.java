// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public abstract class NameResolver {

  public final String packageName;
  protected final Model model;
  protected final ServiceShape serviceShape;
  public final String modelPackage;
  public final CodegenSubject.AwsSdkVersion awsSdkVersion;

  public NameResolver(
    final String packageName,
    final ServiceShape serviceShape,
    final Model model,
    final String modelPackageName,
    CodegenSubject.AwsSdkVersion awsSdkVersion
  ) {
    this.packageName = packageName;
    this.model = model;
    this.serviceShape = serviceShape;
    this.modelPackage = modelPackageName;
    this.awsSdkVersion = awsSdkVersion;
  }

  public boolean isInServiceNameSpace(final ShapeId shapeId) {
    return shapeId.getNamespace().contains(serviceShape.getId().getNamespace());
  }

  public abstract TypeName typeForShape(final ShapeId shapeId);
}
