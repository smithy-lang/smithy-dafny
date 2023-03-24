package software.amazon.polymorph.smithyjava.generator.library;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import software.amazon.polymorph.smithyjava.generator.library.shims.TestServiceShim;
import software.amazon.polymorph.utils.TokenTree;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

public class TestJavaLibrary extends JavaLibrary {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestJavaLibrary.class);

    public TestJavaLibrary(Model model, ServiceShape serviceShape, AwsSdkVersion sdkVersion) {
        super(model, serviceShape, sdkVersion);
    }

    @Override
    public Map<Path, TokenTree> generate() {
        TestServiceShim shim = new TestServiceShim(this, this.serviceShape);
        Map<Path, TokenTree> rtn = new LinkedHashMap<>(shim.generate());
        if (getResourcesInServiceNamespace().size() > 0) {
            // TODO: Support Resources https://sim.amazon.com/issues/CrypTool-5106
            LOGGER.error("--local-service-test does not support Java Resources yet");
        }
        return rtn;
    }
}
