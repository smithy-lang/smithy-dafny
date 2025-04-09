package software.amazon.polymorph.smithygo.localservice;

import java.util.Set;
import java.util.logging.Logger;
import software.amazon.polymorph.smithygo.codegen.EnumGenerator;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.GoSettings;
import software.amazon.polymorph.smithygo.codegen.IntEnumGenerator;
import software.amazon.polymorph.smithygo.codegen.StructureGenerator;
import software.amazon.polymorph.smithygo.codegen.SymbolVisitor;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.directed.CreateContextDirective;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.DirectedCodegen;
import software.amazon.smithy.codegen.core.directed.GenerateEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateErrorDirective;
import software.amazon.smithy.codegen.core.directed.GenerateIntEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.codegen.core.directed.GenerateUnionDirective;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;

public class DafnyLocalServiceDirectedCodegen
  implements DirectedCodegen<GenerationContext, GoSettings, GoIntegration> {

  private static final Logger LOGGER = Logger.getLogger(
    DafnyLocalServiceDirectedCodegen.class.getName()
  );

  @Override
  public SymbolProvider createSymbolProvider(
    CreateSymbolProviderDirective<GoSettings> directive
  ) {
    return new SymbolVisitor(directive.model(), directive.settings());
  }

  @Override
  public GenerationContext createContext(
    CreateContextDirective<GoSettings, GoIntegration> directive
  ) {
    return GenerationContext
      .builder()
      .model(directive.model())
      .settings(directive.settings())
      .symbolProvider(directive.symbolProvider())
      .fileManifest(directive.fileManifest())
      .integrations(directive.integrations())
      .writerDelegator(
        new GoDelegator(directive.fileManifest(), directive.symbolProvider())
      )
      .protocolGenerator(new DafnyLocalServiceTypeConversionProtocol())
      .build();
  }

  @Override
  public void generateService(
    GenerateServiceDirective<GenerationContext, GoSettings> directive
  ) {
    if (
      !directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())
    ) {
      return;
    }
    generateOrphanedShapesForService(directive);
    new DafnyLocalServiceGenerator(directive.context(), directive.service())
      .run();

    var protocolGenerator = directive.context().protocolGenerator();
    if (protocolGenerator == null) {
      return;
    }

    protocolGenerator.generateSerializers(directive.context());

    protocolGenerator.generateDeserializers(directive.context());
  }

  @Override
  public void generateStructure(
    GenerateStructureDirective<GenerationContext, GoSettings> directive
  ) {
    writeStructure(directive.context(), directive.shape());
  }

  @Override
  public void generateError(
    GenerateErrorDirective<GenerationContext, GoSettings> directive
  ) {
    writeStructure(directive.context(), directive.shape());
  }

  public void writeStructure(
    final GenerationContext context,
    final StructureShape shape
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
            final var generator = new StructureGenerator(
              context,
              writer,
              shape
            );
            generator.run();
          }
        );
    }
  }

  @Override
  public void generateUnion(
    GenerateUnionDirective<GenerationContext, GoSettings> directive
  ) {}

  @Override
  public void generateEnumShape(
    GenerateEnumDirective<GenerationContext, GoSettings> directive
  ) {
    writeEnumShape(directive.context(), directive.shape());
  }

  public void writeEnumShape(
    final GenerationContext context,
    final Shape shape
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
            EnumGenerator enumGenerator = new EnumGenerator(
              context.symbolProvider(),
              writer,
              shape
            );
            enumGenerator.run();
          }
        );
    }
  }

  @Override
  public void generateIntEnumShape(
    GenerateIntEnumDirective<GenerationContext, GoSettings> directive
  ) {
    if (
      !directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())
    ) {
      return;
    }
    directive
      .context()
      .writerDelegator()
      .useShapeWriter(
        directive.shape(),
        writer -> {
          IntEnumGenerator intEnumGenerator = new IntEnumGenerator(
            directive.symbolProvider(),
            writer,
            directive.shape().asIntEnumShape().get()
          );
          intEnumGenerator.run();
        }
      );
  }

  /**
   * This MUST run after code generation for non-orphaned shapes.
   * Orphaned shapes may topologically depend on non-orphaned shapes, but not vice versa.
   *
   * @param directive
   */
  protected void generateOrphanedShapesForService(
    final GenerateServiceDirective<GenerationContext, GoSettings> directive
  ) {
    final var orderedShapes =
      ModelUtils.getTopologicallyOrderedOrphanedShapesForService(
        directive.shape(),
        directive.model()
      );
    // Either these shapes are already generated as part of LocalService or doesn't need generation for simple types
    final var shapesToSkip = Set.of(
      ShapeType.OPERATION,
      ShapeType.RESOURCE,
      ShapeType.INTEGER,
      ShapeType.UNION,
      ShapeType.STRING,
      ShapeType.LONG,
      ShapeType.MAP,
      ShapeType.LIST,
      ShapeType.BOOLEAN,
      ShapeType.BLOB
    );

    for (final var shapeToGenerate : orderedShapes) {
      if (shapeToGenerate.isStructureShape()) {
        final var structureShape = shapeToGenerate
          .asStructureShape()
          .orElseThrow();
        writeStructure(directive.context(), structureShape);
      } else if (
        shapeToGenerate.isStringShape() &&
        shapeToGenerate.hasTrait(EnumTrait.class)
      ) {
        writeEnumShape(directive.context(), shapeToGenerate);
      } else if (shapesToSkip.contains(shapeToGenerate.getType())) {
        LOGGER.info(
          "Orphan shape %s is skipped due to configuration.".formatted(
              shapeToGenerate
            )
        );
      } else {
        // Add more as needed...
        throw new ClassCastException(
          "Unsupported class for orphaned shape " + shapeToGenerate
        );
      }
    }
  }
}
