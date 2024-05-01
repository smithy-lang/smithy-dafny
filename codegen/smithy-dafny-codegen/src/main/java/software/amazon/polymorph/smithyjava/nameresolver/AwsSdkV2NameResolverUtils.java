// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import software.amazon.smithy.model.shapes.MemberShape;

public class AwsSdkV2NameResolverUtils {

  /**
   * Returns true if shape is an attribute of an AttributeValue shape; false otherwise
   * @param shape
   * @return true if shape is an attribute of an AttributeValue shape; false otherwise
   */
  public static boolean isAttributeValueType(MemberShape shape) {
    shape.getContainer().getName().equals("AttributeValue");
    String memberName = shape.getMemberName();
    return (
      shape.getContainer().getName().equals("AttributeValue") &&
      (memberName.equals("BOOL") ||
        memberName.equals("NULL") ||
        memberName.equals("L") ||
        memberName.equals("M") ||
        memberName.equals("BS") ||
        memberName.equals("NS") ||
        memberName.equals("SS") ||
        memberName.equals("B") ||
        memberName.equals("N") ||
        memberName.equals("S"))
    );
  }

  public static String tokenToUncapitalizeInShape(MemberShape shape) {
    String memberName = shape.getMemberName();

    if (memberName.startsWith("KMS")) {
      return "KMS";
    }
    if (memberName.startsWith("SSE")) {
      return "SSE";
    }
    if (memberName.startsWith("AWS")) {
      return "AWS";
    }
    return "";
  }
}
