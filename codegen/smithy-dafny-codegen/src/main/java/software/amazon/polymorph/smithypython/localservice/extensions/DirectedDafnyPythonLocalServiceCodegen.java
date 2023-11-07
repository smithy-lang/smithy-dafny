// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.TopologicalIndex;
import software.amazon.smithy.codegen.core.directed.CustomizeDirective;
import software.amazon.smithy.codegen.core.directed.GenerateResourceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.model.neighbor.Walker;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.DirectedPythonCodegen;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.StructureGenerator;
import software.amazon.smithy.python.codegen.SymbolVisitor;

/**
 * DirectedCodegen for Dafny Python wrapped LocalServices.
 * This overrides DirectedPythonCodegen to
 * 1) Not generate a Smithy client (nor its serialize/deserialize bodies, client config, etc.)
 * 2) Remove extraneous generated files (TODO-Python: Consider rewriting SymbolVisitor to avoid this)
 * Wrapped LocalService generation does NOT involve generating a Smithy client;
 *   it will only generate a shim wrapping the LocalService-generated Smithy client.
 */
public class DirectedDafnyPythonLocalServiceCodegen extends DirectedPythonCodegen {

  private static final Logger LOGGER = Logger.getLogger(
      DirectedDafnyPythonLocalServiceCodegen.class.getName());

//  @Override
//  public void customizeBeforeShapeGeneration(
//      CustomizeDirective<GenerationContext, PythonSettings> directive) {
//    GenerationContext context = directive.context();
//    Set<Shape> resourceOperationShapes = context.model().getShapesWithTrait(
//            ReferenceTrait.class).stream()
//        .map(shape -> shape.expectTrait(ReferenceTrait.class).getReferentId())
//        .map(shapeId -> context.model().expectShape(shapeId))
//        .filter(Shape::isResourceShape)
//        .collect(Collectors.toSet());
//    Set<Shape> walkedServiceShapes = new Walker(context.model()).walkShapes(serviceShape);
//    Set<Shape> walkedReferenceShapes = new HashSet<>();
//    for (Shape resourceOperationShape : resourceOperationShapes) {
//      for (Shape walkedShape : new Walker(context.model()).walkShapes(resourceOperationShape)) {
//        walkedReferenceShapes.add(walkedShape);
//      }
//    }
//
//    walkedReferenceShapes.removeAll(walkedServiceShapes);
//
//    for (Shape shape : walkedServiceShapes) {
//      System.out.println("passing to symbolvisitor " + shape.getId());
//      context.protocolGenerator().generate
//      shape.accept(new SymbolVisitor(context.model(), context.settings()));
//    }
//
//    System.out.println("walked");
//    System.out.println(walkedReferenceShapes);
//  }

  /**
   * Do NOT generate any service code for Dafny Python AWS SDKs.
   * Override DirectedPythonCodegen to block any service code generation.
   * In addition to not writing any service code (i.e. not writing `client.py`),
   *   this also blocks writing `serialize.py` and `deserialize.py`.
   * @param directive Directive to perform.
   */
  @Override
  public void generateResource(
      GenerateResourceDirective<GenerationContext, PythonSettings> directive) {
    String moduleName = directive.context().settings().getModuleName();
    directive.context().writerDelegator().useFileWriter(moduleName + "/references.py", "", writer -> {
      new ReferencesFileWriter().generateResourceStuff(directive.shape(), directive.context(), writer);
    });
  }

  @Override
  public void generateStructure(
      GenerateStructureDirective<GenerationContext, PythonSettings> directive) {
    if (directive.shape().hasTrait(ReferenceTrait.class)
        && SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(directive.shape().getId().getNamespace()).equals(directive.settings().getModuleName())) {
      System.out.println("STRUCTURE REFERENCE " + directive.shape().getId());
      Shape ref = directive.model().expectShape(directive.shape().expectTrait(ReferenceTrait.class).getReferentId());
      String moduleName = directive.context().settings().getModuleName();
      directive.context().writerDelegator().useFileWriter(moduleName + "/references.py", "", writer -> {
        new ReferencesFileWriter().generateResourceStuff(ref, directive.context(),
            writer);
      });
    }
    else {
      super.generateStructure(directive);
    }
  }

}
