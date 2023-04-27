package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.integration.GoIntegration;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.CodegenContext;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.utils.SmithyBuilder;

import java.util.ArrayList;
import java.util.List;

public class GoCodegenContext implements CodegenContext<GoSettings, GoWriter, GoIntegration> {
    private final Model model;
    private final GoSettings settings;
    private final SymbolProvider symbolProvider;
    private final FileManifest fileManifest;
    private final GoDelegator writerDelegator;
    private final List<GoIntegration> integrations;

    private GoCodegenContext(Builder builder) {
        model = SmithyBuilder.requiredState("model", builder.model);
        settings = SmithyBuilder.requiredState("settings", builder.settings);
        symbolProvider = SmithyBuilder.requiredState("symbolProvider", builder.symbolProvider);
        fileManifest = SmithyBuilder.requiredState("fileManifest", builder.fileManifest);
        writerDelegator = SmithyBuilder.requiredState("writerDelegator", builder.writerDelegator);
        integrations = SmithyBuilder.requiredState("integrations", builder.integrations);
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
     * Builds {@link GoCodegenContext}s.
     */
    public static final class Builder implements SmithyBuilder<GoCodegenContext> {
        private Model model;
        private GoSettings settings;
        private SymbolProvider symbolProvider;
        private FileManifest fileManifest;
        private GoDelegator writerDelegator;
        private List<GoIntegration> integrations = new ArrayList<>();

        @Override
        public GoCodegenContext build() {
            return new GoCodegenContext(this);
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
    }
}
