// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.JavaFile;
import java.util.LinkedHashSet;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.modeled.ModeledEnum;
import software.amazon.polymorph.smithyjava.modeled.ModeledError;
import software.amazon.polymorph.smithyjava.modeled.ModeledStructure;
import software.amazon.polymorph.smithyjava.modeled.ModeledUnion;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;

/**
 * ModelCodegen generates the content of the Subject's Model package.
 * i.e.: Any POJOs, Enums, Exceptions, or Interfaces that are needed by the Subject.
 * We are following the AWS SDK Java's pattern of placing all of these in
 * a "sub-package", called Model.<p>
 * AWS SDK subject's do NOT need this,
 * as the SDK Library already has all of this defined.<p>
 */
class ModelCodegen extends Generator {

  // Hack to override CodegenSubject
  // Why override? Generator takes any CodegenSubject,
  // but we want the particular subclass JavaLibrary.
  // If we did not hack this,
  // Java would down cast `subject` to CodegenSubject,
  // and we would lose access to any subclass specific APIs or Fields.
  final JavaLibrary subject;
  /** Public Java Interfaces will go here. */
  public final String packageName;
  /** Public POJOs will go here. */
  public final String modelPackageName;

  public ModelCodegen(JavaLibrary subject) {
    super(subject);
    // Hack to override CodegenSubject
    this.subject = subject;
    packageName = subject.packageName;
    modelPackageName = subject.modelPackageName;
  }

  @Override
  public LinkedHashSet<JavaFile> javaFiles() {
    LinkedHashSet<JavaFile> rtn = new LinkedHashSet<>();
    // Opaque Exception Class
    rtn.add(OpaqueError.javaFile(modelPackageName));
    // Collection of Errors class
    rtn.add(CollectionOfErrors.javaFile(modelPackageName));
    // Modeled exception classes
    subject
      .getErrorsInServiceNamespace()
      .stream()
      .map(this::modeledError)
      .forEachOrdered(rtn::add);
    // Structures
    subject
      .getStructuresInServiceNamespace()
      .stream()
      .map(this::modeledStructure)
      .forEachOrdered(rtn::add);
    // Enums
    subject
      .getEnumsInServiceNamespace()
      .stream()
      .map(this::modeledEnum)
      .forEachOrdered(rtn::add);
    // Unions
    subject
      .getUnionsInServiceNamespace()
      .stream()
      .map(this::modeledUnion)
      .forEachOrdered(rtn::add);
    return rtn;
  }

  JavaFile modeledError(StructureShape shape) {
    return ModeledError.javaFile(modelPackageName, shape, subject);
  }

  JavaFile modeledStructure(StructureShape shape) {
    return ModeledStructure.javaFile(modelPackageName, shape, subject);
  }

  JavaFile modeledEnum(Shape shape) {
    return ModeledEnum.javaFile(modelPackageName, shape);
  }

  JavaFile modeledUnion(UnionShape shape) {
    return ModeledUnion.javaFile(modelPackageName, shape, subject);
  }
}
