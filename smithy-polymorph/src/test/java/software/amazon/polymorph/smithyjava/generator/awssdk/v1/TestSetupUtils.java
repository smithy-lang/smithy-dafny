package software.amazon.polymorph.smithyjava.generator.awssdk.v1;

import java.util.function.BiConsumer;

import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;

import static software.amazon.polymorph.utils.AwsSdkNameResolverHelpers.namespaceForService;
import static software.amazon.polymorph.utils.ModelUtils.serviceFromNamespace;

public class TestSetupUtils {
    public static Model setupLocalModel(String rawModel) {
        BiConsumer<ServiceShape.Builder, ModelAssembler> updater;
        updater = ((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", rawModel));
        return TestModel.setupModel(updater);
    }
    public static Model setupTwoLocalModel(String rawModelOne, String rawModelTwo) {
        BiConsumer<ServiceShape.Builder, ModelAssembler> updater;
        updater = ((builder, modelAssembler) -> modelAssembler.addUnparsedModel("testOne.smithy", rawModelOne).addUnparsedModel("testTwo.smithy", rawModelTwo));
        return TestModel.setupModel(updater);
    }
    public static JavaAwsSdkV1 setupAwsSdk(Model localModel, String awsName) {
        ServiceShape serviceShape = serviceFromNamespace(
                localModel, namespaceForService(awsName));
        return JavaAwsSdkV1.createJavaAwsSdkV1(serviceShape, localModel);
    }
    public static JavaLibrary setupLibrary(Model localModel, String namespace) {
        ServiceShape serviceShape = serviceFromNamespace(localModel, namespace);
        return new JavaLibrary(localModel, serviceShape);
    }
}
