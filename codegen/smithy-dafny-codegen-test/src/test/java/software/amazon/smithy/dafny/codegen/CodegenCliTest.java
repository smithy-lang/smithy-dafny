package software.amazon.smithy.dafny.codegen;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.stream.Stream;

class CodegenCliTest {


    @ParameterizedTest
    @ValueSource(strings = {
            "dafny-dependencies/StandardLibrary", // This stores current Polymorph dependencies that all TestModels depend on
            "Aggregate",
            "AggregateReferences",
            "Constraints",
            "Constructor",
            "Dependencies",
            "Errors",
            "Extendable",
            "Extern",
            "LocalService",
            "Refinement",
            "Resource",
            // "SimpleTypes/BigDecimal",
            // "SimpleTypes/BigInteger",
            "SimpleTypes/SimpleBlob",
            "SimpleTypes/SimpleBoolean",
            // "SimpleTypes/SimpleByte",
            "SimpleTypes/SimpleDouble",
            "SimpleTypes/SimpleEnum",
            // "SimpleTypes/SimpleEnumV2",
            // "SimpleTypes/SimpleFloat",
            "SimpleTypes/SimpleInteger",
            "SimpleTypes/SimpleLong",
            // "SimpleTypes/SimpleShort",
            "SimpleTypes/SimpleString",
            // "SimpleTypes/SimpleTimestamp",
            "Union",
            "aws-sdks/ddb",
            "aws-sdks/kms",
            "aws-sdks/sqs-via-cli",
    })
    public void TestModelVerifies(String testModelName) {
        // TODO: Brittle
        File testModelPath = new File("/Users/salkeldr/Documents/GitHub/smithy-dafny/TestModels/" + testModelName);
        Make(testModelPath, "polymorph_dafny");
        Make(testModelPath, "verify");
    }

    private static void Make(File workdir, String... makeArgs) {
        String[] envp = {
            "JAVA_HOME=/Library/Java/JavaVirtualMachines/amazon-corretto-8.jdk/Contents/Home/",
            "PATH=" + System.getenv("PATH")
        };
        String[] args = Stream.concat(Stream.of("make"), Stream.of(makeArgs)).toArray(String[]::new);
        RunCommand(workdir, envp, args);
    }

    private static void RunCommand(File workdir, String[] envp, String[] args) {
        try {
            Runtime rt = Runtime.getRuntime();
            Process pr = rt.exec(args, envp, workdir);
            int exitCode = pr.waitFor();

            ByteArrayOutputStream outBaos = new ByteArrayOutputStream();
            pr.getInputStream().transferTo(outBaos);
            String output = outBaos.toString();

            ByteArrayOutputStream errBaos = new ByteArrayOutputStream();
            pr.getErrorStream().transferTo(errBaos);
            String error = errBaos.toString();

            if (exitCode != 0) {
                throw new AssertionError("Command returned a non-zero error code: " + exitCode
                        + "\n" + output + "\n" + error);
            }
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}