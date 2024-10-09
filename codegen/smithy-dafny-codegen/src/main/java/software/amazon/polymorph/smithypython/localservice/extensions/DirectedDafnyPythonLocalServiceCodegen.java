// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;
import static software.amazon.polymorph.utils.ModelUtils.getTopologicallyOrderedOrphanedShapesForService;

import java.nio.file.Path;
import java.util.List;
import java.util.logging.Logger;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.DafnyLocalServiceCodegenConstants;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.codegen.core.directed.*;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.*;

/**
 * DirectedCodegen for Dafny Python LocalServices. This overrides Smithy-Python's
 * DirectedPythonCodegen behavior. Changes include:
 * - Not writing symbols in a different namespace
 * - Generating a `client.py` file with a synchronous interface
 * - Handling {@link software.amazon.smithy.model.shapes.ResourceShape}s.
 */
public class DirectedDafnyPythonLocalServiceCodegen
  extends DirectedPythonCodegen {

  private static final Logger LOGGER = Logger.getLogger(
    DirectedDafnyPythonLocalServiceCodegen.class.getName()
  );

  @Override
  public SymbolProvider createSymbolProvider(
    CreateSymbolProviderDirective<PythonSettings> directive
  ) {
    return new DafnyPythonLocalServiceSymbolVisitor(
      directive.model(),
      directive.settings()
    );
  }

  @Override
  public void customizeBeforeShapeGeneration(
    CustomizeDirective<GenerationContext, PythonSettings> directive
  ) {
    generateServiceErrors(
      directive.settings(),
      directive.context().writerDelegator()
    );
    new DafnyPythonLocalServiceConfigGenerator(
      directive.settings(),
      directive.context()
    )
      .run();
  }

  /**
   * Override Smithy-Python's generateServiceErrors to generate symbols in the correct directories.
   *
   * @param settings
   * @param writers
   */
  @Override
  protected void generateServiceErrors(
    PythonSettings settings,
    WriterDelegator<PythonWriter> writers
  ) {
    var serviceError = Symbol
      .builder()
      .name("ServiceError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            settings.getService().getNamespace(),
            settings
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            settings.getService().getNamespace()
          )
        )
      )
      .build();
    writers.useFileWriter(
      serviceError.getDefinitionFile(),
      serviceError.getNamespace(),
      writer -> {
        // TODO: subclass a shared error
        writer.openBlock(
          "class $L(Exception):",
          "",
          serviceError.getName(),
          () -> {
            writer.writeDocs("Base error for all errors in the service.");
            writer.write("pass");
          }
        );
      }
    );
    var apiError = Symbol
      .builder()
      .name("ApiError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            settings.getService().getNamespace(),
            settings
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            settings.getService().getNamespace()
          )
        )
      )
      .build();
    writers.useFileWriter(
      apiError.getDefinitionFile(),
      apiError.getNamespace(),
      writer -> {
        writer.addStdlibImport("typing", "Generic");
        writer.addStdlibImport("typing", "TypeVar");
        writer.write("T = TypeVar('T')");
        writer.openBlock(
          "class $L($T, Generic[T]):",
          "",
          apiError.getName(),
          serviceError,
          () -> {
            writer.writeDocs("Base error for all api errors in the service.");
            writer.write("code: T");
            writer.openBlock(
              "def __init__(self, message: str):",
              "",
              () -> {
                writer.write("super().__init__(message)");
                writer.write("self.message = message");
              }
            );
          }
        );

        var unknownApiError = Symbol
          .builder()
          .name("UnknownApiError")
          .namespace(
            format(
              "%s.errors",
              SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                settings.getService().getNamespace(),
                settings
              )
            ),
            "."
          )
          .definitionFile(
            format(
              "./%s/errors.py",
              SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                settings.getService().getNamespace()
              )
            )
          )
          .build();
        writer.addStdlibImport("typing", "Literal");
        writer.openBlock(
          "class $L($T[Literal['Unknown']]):",
          "",
          unknownApiError.getName(),
          apiError,
          () -> {
            writer.writeDocs("Error representing any unknown api errors");
            writer.write("code: Literal['Unknown'] = 'Unknown'");
          }
        );
      }
    );
  }

  /**
   * Override Smithy-Python's generateResource to use Smithy-Dafny-Python resource generation.
   * (Smithy-Python doesn't generate anything for resources.)
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateResource(
    GenerateResourceDirective<GenerationContext, PythonSettings> directive
  ) {
    writeResourceShape(directive.shape(), directive.context());
  }

  protected void writeResourceShape(
    ResourceShape shape,
    GenerationContext context
  ) {
    if (ReferencesFileWriter.shouldGenerateResourceForShape(shape, context)) {
      String moduleName =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          context.settings().getService().getNamespace()
        );
      context
        .writerDelegator()
        .useFileWriter(
          moduleName + "/references.py",
          "",
          writer -> {
            new ReferencesFileWriter()
              .generateResourceInterfaceAndImplementation(
                shape,
                context,
                writer
              );
          }
        );
    }
  }

  /**
   * Override Smithy-Python's generateStructure to not write a symbol in a different namespace.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateStructure(
    GenerateStructureDirective<GenerationContext, PythonSettings> directive
  ) {
    writeStructureShape(directive.shape(), directive.context());
  }

  protected void writeStructureShape(
    StructureShape shape,
    GenerationContext context
  ) {
    if (
      shape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      context
        .writerDelegator()
        .useShapeWriter(
          shape,
          writer -> {
            DafnyPythonLocalServiceStructureGenerator generator =
              new DafnyPythonLocalServiceStructureGenerator(
                context.model(),
                context.settings(),
                context.symbolProvider(),
                writer,
                shape,
                TopologicalIndex.of(context.model()).getRecursiveShapes()
              );
            generator.run();
          }
        );
    }
  }

  /**
   * Override Smithy-Python's generateError to not write a symbol in a different namespace.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateError(
    GenerateErrorDirective<GenerationContext, PythonSettings> directive
  ) {
    writeStructureShapeWithErrorTrait(directive.shape(), directive.context());
  }

  protected void writeStructureShapeWithErrorTrait(
    StructureShape shape,
    GenerationContext context
  ) {
    if (
      shape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      context
        .writerDelegator()
        .useShapeWriter(
          shape,
          writer -> {
            DafnyPythonLocalServiceStructureGenerator generator =
              new DafnyPythonLocalServiceStructureGenerator(
                context.model(),
                context.settings(),
                context.symbolProvider(),
                writer,
                shape,
                TopologicalIndex.of(context.model()).getRecursiveShapes()
              );
            generator.run();
          }
        );
    }
  }

  /**
   * Override Smithy-Python to not write a symbol in a different namespace.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateEnumShape(
    GenerateEnumDirective<GenerationContext, PythonSettings> directive
  ) {
    writeEnumShape(directive.shape(), directive.context());
  }

  protected void writeEnumShape(Shape shape, GenerationContext context) {
    if (
      shape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      EnumShape enumShape;
      if (shape.isEnumShape()) {
        enumShape = shape.asEnumShape().get();
      } else if (shape.isStringShape()) {
        enumShape =
          EnumShape.fromStringShape(shape.asStringShape().get()).get();
      } else {
        throw new IllegalArgumentException(
          "Shape cannot be interpreted as EnumShape: " + shape.getId()
        );
      }

      context
        .writerDelegator()
        .useShapeWriter(
          enumShape,
          writer -> {
            EnumGenerator generator = new EnumGenerator(
              context.model(),
              context.symbolProvider(),
              writer,
              enumShape
            );
            generator.run();
          }
        );
    }
  }

  /**
   * Override Smithy-Python's generateUnion to not write a symbol in a different namespace.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateUnion(
    GenerateUnionDirective<GenerationContext, PythonSettings> directive
  ) {
    writeUnionShape(directive.shape(), directive.context());
  }

  protected void writeUnionShape(UnionShape shape, GenerationContext context) {
    if (
      shape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      context
        .writerDelegator()
        .useShapeWriter(
          shape,
          writer -> {
            DafnyPythonLocalServiceUnionGenerator generator =
              new DafnyPythonLocalServiceUnionGenerator(
                context.model(),
                context.symbolProvider(),
                writer,
                shape,
                TopologicalIndex.of(context.model()).getRecursiveShapes()
              );
            generator.run();
          }
        );
    }
  }

  /**
   * Call `DirectedPythonCodegen.customizeAfterIntegrations`, then remove
   * `localservice_codegen_todelete.py`. The CodegenDirector will invoke this method after shape
   * generation.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void customizeAfterIntegrations(
    CustomizeDirective<GenerationContext, PythonSettings> directive
  ) {
    // DirectedPythonCodegen's customizeAfterIntegrations implementation SHOULD run first;
    //   its implementation writes all files by flushing its writers;
    //   this implementation removes some of those files.
    super.customizeAfterIntegrations(directive);

    FileManifest fileManifest = directive.fileManifest();
    Path generationPath = Path.of(
      fileManifest.getBaseDir() +
      "/" +
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        directive.context().settings().getService().getNamespace()
      )
    );

    /**
     * Smithy ALWAYS writes visited symbols to a file. For AWS SDK codegen, we do NOT want to write
     * visited symbols to a file, since boto3 does not use these visited symbols. It is very, very
     * difficult to change this writing behavior without rewriting Smithy logic in addition to
     * Smithy-Python specific logic. I have tried some workarounds like deleting writers or writing
     * to /dev/null but these were not fruitful. This workaround dumps any visited symbols into a
     * file whose name will never be used and deletes this file as part of its Smithy codegen
     * plugin.
     */
    try {
      LOGGER.info(
        format(
          "Attempting to remove %s.py",
          DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
        )
      );
      CodegenUtils
        .runCommand(
          format(
            "rm -f %s.py",
            DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
          ),
          generationPath
        )
        .strip();
    } catch (CodegenException e) {
      // Fail loudly. We do not want to accidentally distribute this file.
      throw new RuntimeException(
        format(
          "Unable to remove %s.py",
          DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
        ),
        e
      );
    }
  }

  /**
   * This MUST run after code generation for non-orphaned shapes.
   * Orphaned shapes may topologically depend on non-orphaned shapes, but not vice versa.
   *
   * @param directive
   */
  protected void generateOrphanedShapesForService(
    GenerateServiceDirective<GenerationContext, PythonSettings> directive
  ) {
    List<Shape> orderedShapes = getTopologicallyOrderedOrphanedShapesForService(
      directive.shape(),
      directive.model()
    );

    for (Shape shapeToGenerate : orderedShapes) {
      if (shapeToGenerate.isResourceShape()) {
        writeResourceShape(
          shapeToGenerate.asResourceShape().get(),
          directive.context()
        );
      } else if (shapeToGenerate.isStructureShape()) {
        StructureShape structureShape = shapeToGenerate
          .asStructureShape()
          .get();
        if (structureShape.hasTrait(ErrorTrait.class)) {
          writeStructureShapeWithErrorTrait(
            structureShape,
            directive.context()
          );
        } else {
          writeStructureShape(structureShape, directive.context());
        }
      } else if (shapeToGenerate.isEnumShape()) {
        writeEnumShape(
          shapeToGenerate.asEnumShape().get(),
          directive.context()
        );
      } else if (shapeToGenerate.isUnionShape()) {
        writeUnionShape(
          shapeToGenerate.asUnionShape().get(),
          directive.context()
        );
      } else if (shapeToGenerate.isStringShape()) {
        // Classes are not generated for strings
      } else if (shapeToGenerate.isIntegerShape()) {
        // Classes are not generated for ints
      } else if (shapeToGenerate.isListShape()) {
        // Classes are not generated for lists
      } else if (shapeToGenerate.isMapShape()) {
        // Classes are not generated for maps
      } else {
        // Add more as needed...
        throw new ClassCastException(
          "Unsupported class for orphaned shape " + shapeToGenerate
        );
      }
    }
  }

  /**
   * Override Smithy-Python's generateService to generate a synchronous client.
   * Smithy-Python-generated clients' methods are all async.
   * Smithy-Dafny-Python-generated clients' methods are not async.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateService(
    GenerateServiceDirective<GenerationContext, PythonSettings> directive
  ) {
    // For Python, orphaned shape generation MUST run after
    // Smithy-Core's `CodegenDirector.generateShapesInService` executes.
    // Orphaned shapes may depend on shapes generated by that method,
    // and must be generated after non-orphaned shapes.
    // (The reverse is not true; non-orphaned shapes will never depend on orphaned shapes.)
    // Smithy-Core currently calls `directedCodegen.generateService` (this method)
    // immediately after calling `generateShapesInService`,
    // so this is a correct ordering to generate orphaned shapes.
    generateOrphanedShapesForService(directive);

    new SynchronousClientGenerator(directive.context(), directive.service())
      .run();

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
}
