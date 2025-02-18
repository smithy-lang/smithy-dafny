package software.amazon.polymorph.smithygo.codegen;

import java.util.ArrayList;
import java.util.List;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.CodegenContext;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.utils.SmithyBuilder;

public class GenerationContext
  implements CodegenContext<GoSettings, GoWriter, GoIntegration> {

  private final Model model;
  private final GoSettings settings;
  private final SymbolProvider symbolProvider;
  private final FileManifest fileManifest;
  private final GoDelegator writerDelegator;
  private final List<GoIntegration> integrations;
  private final ProtocolGenerator protocolGenerator;

  /**
   * @return Returns the protocol generator to use in code generation.
   */
  public ProtocolGenerator protocolGenerator() {
    return protocolGenerator;
  }

  private GenerationContext(Builder builder) {
    model = SmithyBuilder.requiredState("model", builder.model);
    settings = SmithyBuilder.requiredState("settings", builder.settings);
    symbolProvider =
      SmithyBuilder.requiredState("symbolProvider", builder.symbolProvider);
    fileManifest =
      SmithyBuilder.requiredState("fileManifest", builder.fileManifest);
    writerDelegator =
      SmithyBuilder.requiredState("writerDelegator", builder.writerDelegator);
    integrations =
      SmithyBuilder.requiredState("integrations", builder.integrations);
    protocolGenerator =
      SmithyBuilder.requiredState(
        "protocolGenerator",
        builder.protocolGenerator
      );
  }

  @Override
  public Model model() {
    return model;
  }

  @Override
  public GoSettings settings() {
    return settings;
  }

  @Override
  public SymbolProvider symbolProvider() {
    return symbolProvider;
  }

  @Override
  public FileManifest fileManifest() {
    return fileManifest;
  }

  @Override
  public GoDelegator writerDelegator() {
    return writerDelegator;
  }

  @Override
  public List<GoIntegration> integrations() {
    return integrations;
  }

  /**
   * @return Returns a builder.
   */
  public static Builder builder() {
    return new Builder();
  }

  /**
   * Builds {@link GenerationContext}s.
   */
  public static final class Builder
    implements SmithyBuilder<GenerationContext> {

    private Model model;
    private GoSettings settings;
    private SymbolProvider symbolProvider;
    private FileManifest fileManifest;
    private GoDelegator writerDelegator;
    private List<GoIntegration> integrations = new ArrayList<>();
    private ProtocolGenerator protocolGenerator;

    @Override
    public GenerationContext build() {
      return new GenerationContext(this);
    }

    /**
     * @param model The model being generated.
     * @return Returns the builder.
     */
    public Builder model(Model model) {
      this.model = model;
      return this;
    }

    /**
     * @param settings The resolved settings for the generator.
     * @return Returns the builder.
     */
    public Builder settings(GoSettings settings) {
      this.settings = settings;
      return this;
    }

    /**
     * @param symbolProvider The finalized symbol provider for the generator.
     * @return Returns the builder.
     */
    public Builder symbolProvider(SymbolProvider symbolProvider) {
      this.symbolProvider = symbolProvider;
      return this;
    }

    /**
     * @param fileManifest The file manifest being used in the generator.
     * @return Returns the builder.
     */
    public Builder fileManifest(FileManifest fileManifest) {
      this.fileManifest = fileManifest;
      return this;
    }

    /**
     * @param writerDelegator The writer delegator to use in the generator.
     * @return Returns the builder.
     */
    public Builder writerDelegator(GoDelegator writerDelegator) {
      this.writerDelegator = writerDelegator;
      return this;
    }

    /**
     * @param integrations The integrations to use in the generator.
     * @return Returns the builder.
     */
    public Builder integrations(List<GoIntegration> integrations) {
      this.integrations.clear();
      this.integrations.addAll(integrations);
      return this;
    }

    /**
     * @param protocolGenerator The resolved protocol generator to use.
     * @return Returns the builder.
     */
    public Builder protocolGenerator(ProtocolGenerator protocolGenerator) {
      this.protocolGenerator = protocolGenerator;
      return this;
    }
  }
}
