// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import java.util.logging.Logger;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.codegen.core.directed.*;
import software.amazon.smithy.python.codegen.*;

import static java.lang.String.format;

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

  @Override
  public SymbolProvider createSymbolProvider(
      CreateSymbolProviderDirective<PythonSettings> directive) {
    return new DafnyPythonLocalServiceSymbolVisitor(directive.model(), directive.settings());
  }

    @Override
    public void customizeBeforeShapeGeneration(CustomizeDirective<GenerationContext, PythonSettings> directive) {
        generateServiceErrors(directive.settings(), directive.context().writerDelegator());
        new DafnyPythonLocalServiceConfigGenerator(directive.settings(), directive.context()).run();
    }

    @Override
    protected void generateServiceErrors(PythonSettings settings, WriterDelegator<PythonWriter> writers) {
//        var serviceError = CodegenUtils.getServiceError(settings);
        var serviceError = Symbol.builder()
                .name("ServiceError")
                .namespace(format("%s.errors", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), settings)), ".")
                .definitionFile(format("./%s/errors.py", SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
                .build();
        writers.useFileWriter(serviceError.getDefinitionFile(), serviceError.getNamespace(), writer -> {
            // TODO: subclass a shared error
            writer.openBlock("class $L(Exception):", "", serviceError.getName(), () -> {
                writer.writeDocs("Base error for all errors in the service.");
                writer.write("pass");
            });
        });

//        var apiError = CodegenUtils.getApiError(settings);
        var apiError = Symbol.builder()
                .name("ApiError")
                .namespace(format("%s.errors", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), settings)), ".")
                .definitionFile(format("./%s/errors.py", SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
                .build();
        writers.useFileWriter(apiError.getDefinitionFile(), apiError.getNamespace(), writer -> {
            writer.addStdlibImport("typing", "Generic");
            writer.addStdlibImport("typing", "TypeVar");
            writer.write("T = TypeVar('T')");
            writer.openBlock("class $L($T, Generic[T]):", "", apiError.getName(), serviceError, () -> {
                writer.writeDocs("Base error for all api errors in the service.");
                writer.write("code: T");
                writer.openBlock("def __init__(self, message: str):", "", () -> {
                    writer.write("super().__init__(message)");
                    writer.write("self.message = message");
                });
            });

//            var unknownApiError = CodegenUtils.getUnknownApiError(settings);
            var unknownApiError = Symbol.builder()
                    .name("UnknownApiError")
                    .namespace(format("%s.errors", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), settings)), ".")
                    .definitionFile(format("./%s/errors.py", SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
                    .build();
            writer.addStdlibImport("typing", "Literal");
            writer.openBlock("class $L($T[Literal['Unknown']]):", "", unknownApiError.getName(), apiError, () -> {
                writer.writeDocs("Error representing any unknown api errors");
                writer.write("code: Literal['Unknown'] = 'Unknown'");
            });
        });
    }

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
  if (directive.shape().getId().getNamespace()
          .equals(directive.context().settings().getService().getNamespace())) {
      String moduleName = SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(directive.context().settings().getService().getNamespace());
      directive.context().writerDelegator().useFileWriter(moduleName + "/references.py", "", writer -> {
          new ReferencesFileWriter().generateResourceInterface(directive.shape(), directive.context(), writer);
      });
  }
  }

  @Override
  public void generateStructure(
      GenerateStructureDirective<GenerationContext, PythonSettings> directive) {
    if (directive.shape().getId().getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {

      directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
        DafnyPythonLocalServiceStructureGenerator generator = new DafnyPythonLocalServiceStructureGenerator(
            directive.model(),
            directive.settings(),
            directive.symbolProvider(),
            writer,
            directive.shape(),
            TopologicalIndex.of(directive.model()).getRecursiveShapes()
        );
        generator.run();
      });
    }
  }

    @Override
    public void generateError(GenerateErrorDirective<GenerationContext, PythonSettings> directive) {
        if (directive.shape().getId().getNamespace()
                .equals(directive.context().settings().getService().getNamespace())) {

            directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
                DafnyPythonLocalServiceStructureGenerator generator = new DafnyPythonLocalServiceStructureGenerator(
                        directive.model(),
                        directive.settings(),
                        directive.symbolProvider(),
                        writer,
                        directive.shape(),
                        TopologicalIndex.of(directive.model()).getRecursiveShapes()
                );
                generator.run();
            });
        }
    }

  @Override
  public void generateUnion(
      GenerateUnionDirective<GenerationContext, PythonSettings> directive) {
    if (directive.shape().getId().getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {

      directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
        UnionGenerator generator = new UnionGenerator(
            directive.model(),
            directive.symbolProvider(),
            writer,
            directive.shape(),
            TopologicalIndex.of(directive.model()).getRecursiveShapes()
        );
        generator.run();
      });
    }
  }

  @Override
  public void generateService(GenerateServiceDirective<GenerationContext, PythonSettings> directive) {
      new SynchronousClientGenerator(directive.context(), directive.service()).run();

      var protocolGenerator = directive.context().protocolGenerator();
      if (protocolGenerator == null) {
          return;
      }

      protocolGenerator.generateSharedSerializerComponents(directive.context());
      protocolGenerator.generateRequestSerializers(directive.context());

      protocolGenerator.generateSharedDeserializerComponents(directive.context());
      protocolGenerator.generateResponseDeserializers(directive.context());

      protocolGenerator.generateProtocolTests(directive.context());
  }



//    if (directive.shape().hasTrait(ReferenceTrait.class)
//      && directive.shape().getId().getNamespace().equals(directive.context().settings().getService().getNamespace())) {
////        && SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(directive.shape().getId().getNamespace()).equals(directive.settings().getModuleName())) {
//      System.out.println("STRUCTURE REFERENCE " + directive.shape().getId());
//      Shape ref = directive.model().expectShape(directive.shape().expectTrait(ReferenceTrait.class).getReferentId());
//      String moduleName = directive.context().settings().getModuleName();
//      directive.context().writerDelegator().useFileWriter(moduleName + "/references.py", "", writer -> {
//        // TOOD: Services are different.
//        // NEED TO GENERATESERVICESTUFF.
//        if (ref.isResourceShape()) {
//          new ReferencesFileWriter().generateResourceStuff(ref, directive.context(),
//              writer);
//        } else if (ref.isServiceShape()) {
//          new ReferencesFileWriter().customizeFileForServiceShape(ref.asServiceShape().get(), directive.context());
//        }
//
//      });
//    }
//    else {
//      if (directive.shape().getId().getNamespace().equals(directive.context().settings().getService().getNamespace())) {
//        super.generateStructure(directive);
//
//      }
//    }



}
