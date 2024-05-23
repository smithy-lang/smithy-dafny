package software.amazon.polymorph.smithyrust.generator;

import software.amazon.smithy.rust.codegen.client.smithy.ClientCodegenContext;
import software.amazon.smithy.rust.codegen.client.smithy.generators.OperationGenerator;
import software.amazon.smithy.rust.codegen.core.smithy.generators.protocol.ProtocolSupport;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.Protocol;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.ProtocolGeneratorFactory;

public class LocalServiceProtocolFactory implements ProtocolGeneratorFactory<OperationGenerator, ClientCodegenContext> {
    @Override
    public OperationGenerator buildProtocolGenerator(ClientCodegenContext codegenContext) {
        return new OperationGenerator(codegenContext, protocol(codegenContext), null);
    }

    @Override
    public Protocol protocol(ClientCodegenContext clientCodegenContext) {
        return new LocalServiceProtocol();
    }

    @Override
    public ProtocolSupport support() {
        return new ProtocolSupport(false, false, false, false, false, false, false, false);
    }
}
