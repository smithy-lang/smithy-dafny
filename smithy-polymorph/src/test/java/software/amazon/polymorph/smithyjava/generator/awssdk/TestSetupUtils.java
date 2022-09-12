package software.amazon.polymorph.smithyjava.generator.awssdk;

import java.util.function.BiConsumer;

import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;

import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkHelpers.namespaceForService;
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
    public static AwsSdk setupAwsSdk(Model localModel, String awsName) {
        ServiceShape serviceShape = serviceFromNamespace(
                localModel, namespaceForService(awsName));
        return new AwsSdk(serviceShape, localModel);
    }
}
