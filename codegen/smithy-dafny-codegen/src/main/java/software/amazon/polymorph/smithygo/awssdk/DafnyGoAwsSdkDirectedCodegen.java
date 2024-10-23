package software.amazon.polymorph.smithygo.awssdk;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.GoSettings;
import software.amazon.polymorph.smithygo.codegen.SymbolVisitor;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
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

public class DafnyGoAwsSdkDirectedCodegen
  implements DirectedCodegen<GenerationContext, GoSettings, GoIntegration> {

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
      .protocolGenerator(
        new DafnyAwsSdkClientTypeConversionProtocol(
          directive.model(),
          directive.service()
        )
      )
      .build();
  }

  @Override
  public void generateService(
    GenerateServiceDirective<GenerationContext, GoSettings> directive
  ) {
    new DafnyAwsSdkClientShimGenerator(directive.context(), directive.service())
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
    GenerateStructureDirective<
      GenerationContext,
      GoSettings
    > generateStructureDirective
  ) {}

  @Override
  public void generateError(
    GenerateErrorDirective<GenerationContext, GoSettings> generateErrorDirective
  ) {}

  @Override
  public void generateUnion(
    GenerateUnionDirective<GenerationContext, GoSettings> generateUnionDirective
  ) {}

  @Override
  public void generateEnumShape(
    GenerateEnumDirective<GenerationContext, GoSettings> generateEnumDirective
  ) {}

  @Override
  public void generateIntEnumShape(
    GenerateIntEnumDirective<
      GenerationContext,
      GoSettings
    > generateIntEnumDirective
  ) {}
}
