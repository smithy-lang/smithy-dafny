// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import static java.util.function.Function.identity;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.junit.jupiter.api.Assumptions;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.smithy.utils.IoUtils;

/**
 * An abstract base class for a test that should be run on every test model,
 * unless it isn't supported yet for a particular subset of those models.
 */
public abstract class TestModelTest {

  protected static Stream<String> discoverTestModels() throws IOException {
    var testModelRoot = Paths
      .get(".")
      .resolve("..")
      .resolve("..")
      .resolve("TestModels");
    var allTestModels = Files
      .walk(testModelRoot)
      .filter(p ->
        Files.exists(p.resolve("Makefile")) &&
        (Files.isDirectory(p.resolve("Model")) ||
          Files.isDirectory(p.resolve("model")))
      )
      .map(testModelRoot::relativize)
      .map(Path::toString);

    return selectShard(allTestModels);
  }

  private static Stream<String> selectShard(Stream<String> list) {
    var sorted = list.sorted().toList();

    // Select the requested fraction of the test collections if using the JUNIT_SHARD[_COUNT] environment variables.
    var shardEnvVar = System.getenv("JUNIT_SHARD");
    var numShardsEnvVar = System.getenv("JUNIT_SHARD_COUNT");
    if (shardEnvVar != null || numShardsEnvVar != null) {
      if (shardEnvVar == null || numShardsEnvVar == null) {
        throw new IllegalArgumentException(
          "The JUNIT_SHARD and JUNIT_SHARD_COUNT environment variables must both be provided."
        );
      }

      var shard = Integer.parseInt(shardEnvVar);
      var numShards = Integer.parseInt(numShardsEnvVar);
      if (numShards <= 0) {
        throw new IllegalArgumentException(
          "JUNIT_SHARD_COUNT must be greater than 0."
        );
      }
      if (shard <= 0 || shard > numShards) {
        throw new IllegalArgumentException(
          "JUNIT_SHARD must be at least 1 and at most JUNIT_SHARD_COUNT."
        );
      }

      return IntStream
        .range(0, sorted.size())
        .filter(index -> index % numShards == shard - 1)
        .mapToObj(sorted::get);
    }

    return sorted.stream();
  }

  protected Path getTestModelPath(String relativeTestModelPath) {
    return Paths
      .get(".")
      .resolve("..")
      .resolve("..")
      .resolve("TestModels")
      .resolve(relativeTestModelPath);
  }

  protected void testModels(String relativeTestModelPath) {
    // The @streaming support depends on our subset of the Dafny standard libraries
    // which cannot be built for old versions of Dafny.
    if (
      relativeTestModelPath.endsWith("Streaming") ||
      relativeTestModelPath.endsWith("s3")
    ) {
      DafnyVersion dafnyVersion = CodegenEngine.getDafnyVersionFromDafny();
      if (dafnyVersion.compareTo(DafnyVersion.parse("4.9.0")) < 0) {
        Assumptions.assumeTrue(false);
      }
    }
  }
}
