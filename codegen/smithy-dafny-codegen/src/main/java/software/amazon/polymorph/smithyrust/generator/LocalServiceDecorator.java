package software.amazon.polymorph.smithyrust.generator;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.rust.codegen.client.smithy.ClientCodegenContext;
import software.amazon.smithy.rust.codegen.client.smithy.ClientRustSettings;
import software.amazon.smithy.rust.codegen.client.smithy.customize.AuthSchemeOption;
import software.amazon.smithy.rust.codegen.client.smithy.customize.ClientCodegenDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.endpoint.EndpointCustomization;
import software.amazon.smithy.rust.codegen.client.smithy.generators.OperationCustomization;
import software.amazon.smithy.rust.codegen.client.smithy.generators.OperationGenerator;
import software.amazon.smithy.rust.codegen.client.smithy.generators.ServiceRuntimePluginSection;
import software.amazon.smithy.rust.codegen.client.smithy.generators.config.ServiceConfig;
import software.amazon.smithy.rust.codegen.client.smithy.generators.error.ErrorCustomization;
import software.amazon.smithy.rust.codegen.client.smithy.generators.protocol.ProtocolTestGenerator;
import software.amazon.smithy.rust.codegen.core.rustlang.RustWriter;
import software.amazon.smithy.rust.codegen.core.smithy.ModuleDocProvider;
import software.amazon.smithy.rust.codegen.core.smithy.RustCrate;
import software.amazon.smithy.rust.codegen.core.smithy.RustSymbolProvider;
import software.amazon.smithy.rust.codegen.core.smithy.customize.AdHocSection;
import software.amazon.smithy.rust.codegen.core.smithy.customize.NamedCustomization;
import software.amazon.smithy.rust.codegen.core.smithy.generators.BuilderCustomization;
import software.amazon.smithy.rust.codegen.core.smithy.generators.LibRsSection;
import software.amazon.smithy.rust.codegen.core.smithy.generators.StructureCustomization;
import software.amazon.smithy.rust.codegen.core.smithy.generators.error.ErrorImplCustomization;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.ProtocolGeneratorFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class LocalServiceDecorator implements ClientCodegenDecorator {
    @Override
    public Map<ShapeId, ProtocolGeneratorFactory<OperationGenerator, ClientCodegenContext>> protocols(ShapeId serviceId, Map<ShapeId, ? extends ProtocolGeneratorFactory<? extends OperationGenerator, ClientCodegenContext>> currentProtocols) {
        Map<ShapeId, ProtocolGeneratorFactory<OperationGenerator, ClientCodegenContext>> result = new HashMap<>();
        // TODO: generics are making it hard to putAll(currentProtocols), but we don't actually need any of those protocols anyway :)
        result.put(ShapeId.fromParts("aws.polymorph", "localService"), new LocalServiceProtocolFactory());
        return result;
    }

    // TODO: Hook up Kotlin interface defaults as needed

    @Override
    public kotlin.jvm.functions.Function1<RustWriter, kotlin.Unit> clientConstructionDocs(ClientCodegenContext clientCodegenContext, kotlin.jvm.functions.Function1<? super RustWriter, kotlin.Unit> function1) {
        return null;
    }

    @Override
    public List<AuthSchemeOption> authOptions(ClientCodegenContext clientCodegenContext, OperationShape operationShape, List<? extends AuthSchemeOption> list) {
        return null;
    }

    @Override
    public List<NamedCustomization<ServiceConfig>> configCustomizations(ClientCodegenContext clientCodegenContext, List<? extends NamedCustomization<ServiceConfig>> list) {
        return null;
    }

    @Override
    public List<EndpointCustomization> endpointCustomizations(ClientCodegenContext clientCodegenContext) {
        return null;
    }

    @Override
    public List<ErrorCustomization> errorCustomizations(ClientCodegenContext clientCodegenContext, List<? extends ErrorCustomization> list) {
        return null;
    }

    @Override
    public List<OperationCustomization> operationCustomizations(ClientCodegenContext clientCodegenContext, OperationShape operationShape, List<? extends OperationCustomization> list) {
        return null;
    }

    @Override
    public ProtocolTestGenerator protocolTestGenerator(ClientCodegenContext clientCodegenContext, ProtocolTestGenerator protocolTestGenerator) {
        return null;
    }

    @Override
    public List<NamedCustomization<ServiceRuntimePluginSection>> serviceRuntimePluginCustomizations(ClientCodegenContext clientCodegenContext, List<? extends NamedCustomization<ServiceRuntimePluginSection>> list) {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    @Override
    public byte getOrder() {
        return 0;
    }

    @Override
    public List<BuilderCustomization> builderCustomizations(ClientCodegenContext clientCodegenContext, List<? extends BuilderCustomization> list) {
        return null;
    }

    @Override
    public boolean classpathDiscoverable() {
        return false;
    }

    @Override
    public Map<String, Object> crateManifestCustomizations(ClientCodegenContext clientCodegenContext) {
        return null;
    }

    @Override
    public List<ErrorImplCustomization> errorImplCustomizations(ClientCodegenContext clientCodegenContext, List<? extends ErrorImplCustomization> list) {
        return null;
    }

    @Override
    public List<NamedCustomization<AdHocSection>> extraSections(ClientCodegenContext clientCodegenContext) {
        return null;
    }

    @Override
    public void extras(ClientCodegenContext clientCodegenContext, RustCrate rustCrate) {

    }

    @Override
    public List<NamedCustomization<LibRsSection>> libRsCustomizations(ClientCodegenContext clientCodegenContext, List<? extends NamedCustomization<LibRsSection>> list) {
        return null;
    }

    @Override
    public ModuleDocProvider moduleDocumentationCustomization(ClientCodegenContext clientCodegenContext, ModuleDocProvider moduleDocProvider) {
        return null;
    }

    @Override
    public List<StructureCustomization> structureCustomizations(ClientCodegenContext clientCodegenContext, List<? extends StructureCustomization> list) {
        return null;
    }

    @Override
    public RustSymbolProvider symbolProvider(RustSymbolProvider rustSymbolProvider) {
        return null;
    }

    @Override
    public Model transformModel(ServiceShape serviceShape, Model model, ClientRustSettings clientRustSettings) {
        return null;
    }
}
