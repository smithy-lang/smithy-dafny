package software.amazon.polymorph.smithyjava.generator.awssdk;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV1;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV1;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * Generates all the Java Classes needed for
 * Dafny Generated Java to call AWS Services via
 * the AWS SDK for Java V1.
 */
public class AwsSdkV1 extends CodegenSubject {

    public AwsSdkV1(ServiceShape serviceShape, Model model) {
        super(
                model,
                serviceShape,
                new AwsSdkDafnyV1(serviceShape, model),
                new AwsSdkNativeV1(serviceShape, model)
        );
    }

    public Map<Path, TokenTree> generate() {
        Map<Path, TokenTree> rtn = new HashMap<>();
        ShimV1 shimGenerator = new ShimV1(this);
        ToDafny toDafnyGenerator = new ToDafny(this);
        ToNative toNativeGenerator = new ToNative(this);
        rtn.putAll(shimGenerator.generate());
        rtn.putAll(toDafnyGenerator.generate());
        rtn.putAll(toNativeGenerator.generate());
        return rtn;
    }

}
