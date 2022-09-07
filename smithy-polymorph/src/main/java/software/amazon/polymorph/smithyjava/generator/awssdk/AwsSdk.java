package software.amazon.polymorph.smithyjava.generator.awssdk;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafny;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNative;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * Generates all the Java Classes needed for
 * Dafny Generated Java to call AWS Services via
 * the AWS SDK for Java V1.
 */
public class AwsSdk {
    AwsSdkDafny dafnyNameResolver;
    AwsSdkNative nativeNameResolver;
    Model model;
    ServiceShape serviceShape;

    public AwsSdk(ServiceShape serviceShape, Model model) {
        this.serviceShape = serviceShape;
        this.dafnyNameResolver = new AwsSdkDafny(serviceShape, model);
        this.nativeNameResolver = new AwsSdkNative(serviceShape, model);
        this.model = model;
    }

    public Map<Path, TokenTree> generate() {
        Map<Path, TokenTree> rtn = new HashMap<>();
        Shim shimGenerator = new Shim(this);
        ToDafny toDafnyGenerator = new ToDafny(this);
        ToNative toNativeGenerator = new ToNative(this);
        rtn.putAll(shimGenerator.generate());
        rtn.putAll(toDafnyGenerator.generate());
        rtn.putAll(toNativeGenerator.generate());
        return rtn;
    }

}
