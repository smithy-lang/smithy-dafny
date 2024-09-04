package software.amazon.polymorph.smithygo.localservice;

import java.util.logging.Logger;
import software.amazon.polymorph.smithygo.codegen.EnumGenerator;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.GoSettings;
import software.amazon.polymorph.smithygo.codegen.IntEnumGenerator;
import software.amazon.polymorph.smithygo.codegen.StructureGenerator;
import software.amazon.polymorph.smithygo.codegen.SymbolVisitor;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.directed.CreateContextDirective;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.DirectedCodegen;
import software.amazon.smithy.codegen.core.directed.GenerateEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateErrorDirective;
import software.amazon.smithy.codegen.core.directed.GenerateIntEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateResourceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.codegen.core.directed.GenerateUnionDirective;

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
          StructureGenerator generator = new StructureGenerator(
            directive.context(),
            writer,
            directive.shape()
          );
          generator.run();
        }
      );
  }

  @Override
  public void generateError(
    GenerateErrorDirective<GenerationContext, GoSettings> directive
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
          StructureGenerator generator = new StructureGenerator(
            directive.context(),
            writer,
            directive.shape()
          );
          generator.run();
        }
      );
  }

  @Override
  public void generateUnion(
    GenerateUnionDirective<GenerationContext, GoSettings> directive
  ) {}

  @Override
  public void generateEnumShape(
    GenerateEnumDirective<GenerationContext, GoSettings> directive
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
          EnumGenerator enumGenerator = new EnumGenerator(
            directive.symbolProvider(),
            writer,
            directive.shape()
          );
          enumGenerator.run();
        }
      );
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

  @Override
  public void generateResource(
    GenerateResourceDirective<GenerationContext, GoSettings> directive
  ) {
    //        System.out.println("##############" + directive.shape());
    //        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
    //        });
  }
}
