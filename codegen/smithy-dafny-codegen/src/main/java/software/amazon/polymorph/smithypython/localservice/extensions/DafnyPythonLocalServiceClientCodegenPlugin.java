// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.JavaDocTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.AbstractShapeBuilder;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

import java.util.Map;

/**
 * Plugin to trigger Smithy-Dafny Python code generation.
 * This differs from the PythonClientCodegenPlugin by not calling
 *     runner.performDefaultCodegenTransforms();
 * and
 *     runner.createDedicatedInputsAndOutputs();
 * These methods transform the model in ways that the model does not align with
 *   the generated Dafny code.
 */
@SmithyUnstableApi
public final class DafnyPythonLocalServiceClientCodegenPlugin implements SmithyBuildPlugin {

  public DafnyPythonLocalServiceClientCodegenPlugin(Map<String, String> smithyNamespaceToPythonModuleNameMap) {
    super();
    System.out.println("smithyNamespaceToPythonModuleNameMap");
    System.out.println(smithyNamespaceToPythonModuleNameMap.entrySet());
    SmithyNameResolver.setSmithyNamespaceToPythonModuleNameMap(smithyNamespaceToPythonModuleNameMap);
  }

  @Override
  public String getName() {
    return "dafny-python-localservice-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<PythonWriter, PythonIntegration, GenerationContext, PythonSettings> runner
        = new CodegenDirector<>();

    PythonSettings settings = PythonSettings.from(context.getSettings());
    runner.settings(settings);
    runner.directedCodegen(new DirectedDafnyPythonLocalServiceCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.service(settings.getService());
    runner.model(context.getModel());
    runner.integrationClass(PythonIntegration.class);

    ServiceShape serviceShape = context.getModel().expectShape(settings.getService()).asServiceShape().get();
    Model transformedModel = transformServiceShapeToAddReferenceResources(context.getModel(), serviceShape);
    transformedModel = transformServiceShapeToAddDocumentationTraits(transformedModel);
    runner.model(transformedModel);

    runner.run();
  }

  public static Model transformServiceShapeToAddDocumentationTraits(Model model) {
    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.hasTrait(JavaDocTrait.class)) {
        JavaDocTrait javaDocTrait = shape.getTrait(JavaDocTrait.class).get();
        System.out.println("javadoc trait value: " + javaDocTrait.getValue());
        DocumentationTrait documentationTrait = new DocumentationTrait(javaDocTrait.getValue());
        // Wow, this is brutal, but there is no Shape.Builder interface to abstract this away here...

        AbstractShapeBuilder<?,?> builder;
        if (shape.isStructureShape()) {
          builder = shape.asStructureShape().get().toBuilder();
        } else if (shape.isStringShape()) {
          builder = shape.asStringShape().get().toBuilder();
        } else if (shape.isMemberShape()) {
          builder = shape.asMemberShape().get().toBuilder();
        } else if (shape.isResourceShape()) {
          builder = shape.asResourceShape().get().toBuilder();
        } else if (shape.isServiceShape()) {
          builder = shape.asServiceShape().get().toBuilder();
        } else if (shape.isBlobShape()) {
          builder = shape.asBlobShape().get().toBuilder();
        } else if (shape.isEnumShape()) {
          builder = shape.asEnumShape().get().toBuilder();
        } else if (shape.isIntegerShape()) {
          builder = shape.asIntegerShape().get().toBuilder();
        } else if (shape.isOperationShape()) {
          builder = shape.asOperationShape().get().toBuilder();
        } else {
          // Unfortunately, there is no "default" shape...
          throw new IllegalArgumentException("Javadoc trait on unsupported shape: " + shape);
        }
        builder.addTrait(documentationTrait);
        return builder.build();
      } else {
        return shape;
      }
    });
  }

  public static Model transformServiceShapeToAddReferenceResources(Model model, ServiceShape serviceShape) {

    ServiceShape.Builder transformedServiceShapeBuilder = serviceShape.toBuilder();
    ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.hasTrait(ReferenceTrait.class)) {

        ShapeId referenceShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
        if (model.expectShape(referenceShapeId).isResourceShape()) {
          transformedServiceShapeBuilder.addResource(referenceShapeId);
        }
      }
      return shape;
    });

    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.equals(serviceShape)) {
        return transformedServiceShapeBuilder.build();
      } else {
        return shape;
      }
    });
  }
}