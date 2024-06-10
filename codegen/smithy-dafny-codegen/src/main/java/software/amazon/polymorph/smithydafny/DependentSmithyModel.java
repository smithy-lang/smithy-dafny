// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import java.nio.file.Path;
import java.util.stream.Stream;
import software.amazon.smithy.model.shapes.Shape;

public record DependentSmithyModel(Path modelPath, String namespace)
  implements Comparable<DependentSmithyModel> {
  public static DependentSmithyModel of(final Shape shape, Path[] modelPaths) {
    final String namespace = shape.getId().getNamespace();
    final Path sourceLocation = Path.of(
      shape.getSourceLocation().getFilename()
    );
    final Path modelPath = Stream
      .of(modelPaths)
      .filter(sourceLocation::startsWith)
      .reduce((a, b) -> {
        throw new IllegalStateException(
          "A dependent model can not be a sub directory of another dependent model"
        );
      })
      .get();

    return new DependentSmithyModel(modelPath, namespace);
  }

  @Override
  public int compareTo(DependentSmithyModel dependentSmithyModel) {
    return this.modelPath.compareTo(dependentSmithyModel.modelPath);
  }
}
