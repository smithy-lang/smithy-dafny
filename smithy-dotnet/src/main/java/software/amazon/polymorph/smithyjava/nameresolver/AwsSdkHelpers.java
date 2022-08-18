package software.amazon.polymorph.smithyjava.nameresolver;

public class AwsSdkHelpers {
    public static String namespaceForService(final String awsServiceName) {
        return "com.amazonaws.%s".formatted(awsServiceName);
    }
}
