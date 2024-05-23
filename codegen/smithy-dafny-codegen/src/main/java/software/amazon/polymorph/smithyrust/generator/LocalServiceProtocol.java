package software.amazon.polymorph.smithyrust.generator;

import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.TimestampFormatTrait;
import software.amazon.smithy.rust.codegen.core.smithy.RuntimeType;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.HttpBindingResolver;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.Protocol;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.parse.StructuredDataParserGenerator;
import software.amazon.smithy.rust.codegen.core.smithy.protocols.serialize.StructuredDataSerializerGenerator;

import java.util.List;

public class LocalServiceProtocol implements Protocol {
    @Override
    public TimestampFormatTrait.Format getDefaultTimestampFormat() {
        return null;
    }

    @Override
    public HttpBindingResolver getHttpBindingResolver() {
        return null;
    }

    @Override
    public List<kotlin.Pair<String, String>> additionalErrorResponseHeaders(StructureShape structureShape) {
        return null;
    }

    @Override
    public List<kotlin.Pair<String, String>> additionalRequestHeaders(OperationShape operationShape) {
        return null;
    }

    @Override
    public RuntimeType parseEventStreamErrorMetadata(OperationShape operationShape) {
        return null;
    }

    @Override
    public RuntimeType parseHttpErrorMetadata(OperationShape operationShape) {
        return null;
    }

    @Override
    public StructuredDataParserGenerator structuredDataParser() {
        return null;
    }

    @Override
    public StructuredDataSerializerGenerator structuredDataSerializer() {
        return null;
    }
}
