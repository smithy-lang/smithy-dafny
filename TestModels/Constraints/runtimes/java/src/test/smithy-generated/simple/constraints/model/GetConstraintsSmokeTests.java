// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints.model;

import java.lang.String;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.HashMap;
import org.testng.Assert;
import org.testng.annotations.Test;
import simple.constraints.SimpleConstraints;

public final class GetConstraintsSmokeTests {
  @Test
  public void GetConstraintsSuccess() {
    SimpleConstraintsConfig config = SimpleConstraintsConfig.builder().build();
    SimpleConstraints client = SimpleConstraints.builder().SimpleConstraintsConfig(config).build();
    GetConstraintsInput input = GetConstraintsInput.builder()
        .OneToTen(5)
        .GreaterThanOne(2)
        .MyBlob(ByteBuffer.wrap("0101".getBytes(StandardCharsets.US_ASCII)))
        .MyList(Arrays.asList("1", "2", "3"))
        .MyMap(new HashMap<String, String>() {{
        put("a", "b");
        put("c", "d");
        }})
        .build();
    client.GetConstraints(input);
  }

  @Test
  public void GetConstraintsFailure() {
    SimpleConstraintsConfig config = SimpleConstraintsConfig.builder().build();
    SimpleConstraints client = SimpleConstraints.builder().SimpleConstraintsConfig(config).build();
    Assert.assertThrows(Exception.class, () -> {
        simple.constraints.model.GetConstraintsInput input = simple.constraints.model.GetConstraintsInput.builder()
            .OneToTen(5)
            .GreaterThanOne(2)
            .NonEmptyBlob(java.nio.ByteBuffer.wrap("".getBytes(java.nio.charset.StandardCharsets.US_ASCII)))
            .build();
        client.GetConstraints(input);

        });
  }
}
