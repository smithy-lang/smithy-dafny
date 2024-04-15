// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

public class NamespaceHelper {

  /**
   * Crypto Tools has used the namespace `aws.cryptography` in our Smithy Models;
   * <p>But AWS Java uses `software.amazon` instead of `aws`.*/
  // Historically, we have used `encryption` instead of `cryptography`,
  // but we are more flexible w.r.t. encryption vs cryptography.
  public static String standardize(String namespace) {
    String rtn = namespace.toLowerCase();
    if (namespace.startsWith("aws")) {
      rtn = rtn.replaceFirst("aws", "software.amazon");
    } else if (namespace.startsWith("com.amazonaws")) {
      rtn =
        rtn.replaceFirst(
          "com.amazonaws",
          "software.amazon.cryptography.services"
        );
    }
    return rtn;
  }
}
