// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.common.customize;

import java.util.Set;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;

/** Interface for writing custom Dafny-Python code to files. */
public interface CustomFileWriter {
  /**
   * Writes code specific to the file targeted by the CustomFileWriter for the provided
   * ServiceShape. The ServiceShape SHOULD be a shape annotated with the
   * `aws.polymorph#localService` trait.
   *
   * @param serviceShape
   * @param codegenContext
   */
  default void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {}
}
