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
public class JavaAwsSdkV1 extends CodegenSubject {
    // Hack to override Name Resolvers to Aws Sdk V1 specific ones
    // See code comment on ../library/ModelCodegen for details.
    final AwsSdkDafnyV1 dafnyNameResolver;
    final AwsSdkNativeV1 nativeNameResolver;

    public JavaAwsSdkV1(ServiceShape serviceShape, Model model) {
        super(
                model,
                serviceShape,
                new AwsSdkDafnyV1(serviceShape, model),
                new AwsSdkNativeV1(serviceShape, model)
        );
        this.dafnyNameResolver = new AwsSdkDafnyV1(serviceShape, model);
        this.nativeNameResolver = new AwsSdkNativeV1(serviceShape, model);
    }

    public Map<Path, TokenTree> generate() {
        Map<Path, TokenTree> rtn = new HashMap<>();
        ShimV1 shimGenerator = new ShimV1(this);
        ToDafnyAwsV1 toDafnyGenerator = new ToDafnyAwsV1(this);
        ToNativeAwsV1 toNativeGenerator = new ToNativeAwsV1(this);
        rtn.putAll(shimGenerator.generate());
        rtn.putAll(toDafnyGenerator.generate());
        rtn.putAll(toNativeGenerator.generate());
        return rtn;
    }

}
