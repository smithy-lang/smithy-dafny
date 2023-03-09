package software.amazon.smithy.dafny.codegen.runtime.java;

public class NamespaceHelper {
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
