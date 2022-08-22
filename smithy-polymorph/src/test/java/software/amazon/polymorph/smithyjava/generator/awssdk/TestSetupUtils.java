package software.amazon.polymorph.smithyjava.generator.awssdk;

import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkHelpers.namespaceForService;
import static software.amazon.polymorph.utils.ModelUtils.serviceFromNamespace;

public class TestSetupUtils {
    public static AwsSdk setupAwsSdk(String rawModel, String awsName) {
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        ServiceShape serviceShape = serviceFromNamespace(
                localModel, namespaceForService(awsName));
        return new AwsSdk(serviceShape, localModel);
    }
}
