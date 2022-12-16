package software.amazon.polymorph.smithyjava;

public class NamespaceHelper {
    public final static String AWS_SERVICE_NAMESPACE_PREFIX = "com.amazonaws";

    /**
     * Crypto Tools has used the namespace `aws.cryptography` in our Smithy Models;
     * <p>But AWS Java uses `software.amazon` instead of `aws`.
     * <p>We have tended to use `encryption` instead of `cryptography`,
     * but we are more flexible here.
     */
    public static String standardize(String namespace) {
        String rtn = namespace;
        if (namespace.startsWith("aws")) {
            rtn = rtn.replaceFirst("aws", "software.amazon");
        }
        return rtn;
    }
}
