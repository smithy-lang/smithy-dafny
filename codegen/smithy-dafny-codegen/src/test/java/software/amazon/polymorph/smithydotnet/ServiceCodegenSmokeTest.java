// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.*;

import java.net.URL;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.junit.Test;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class ServiceCodegenSmokeTest {

  // TODO: Apply ServiceCodegen changes to tests
  // https://github.com/smithy-lang/smithy-dafny/issues/27
  @Test
  public void testCorrectFilesGenerated() {
    final URL modelUrl = Objects.requireNonNull(
      this.getClass().getClassLoader().getResource("model.smithy")
    );
    final ModelAssembler assembler = new ModelAssembler();
    ModelUtils.addCustomTraitsToModelAssembler(assembler);
    final Model model = assembler.addImport(modelUrl).assemble().unwrap();

    final ShapeId serviceShapeId = ShapeId.fromParts(
      "polymorph.demo",
      "StringLists"
    );
    final ServiceShape serviceShape = model.expectShape(
      serviceShapeId,
      ServiceShape.class
    );
    final ServiceCodegen serviceCodegen = new ServiceCodegen(
      model,
      serviceShape
    );
    final Map<Path, TokenTree> codeByPath = serviceCodegen.generate();

    final Set<Path> expectedPaths = Stream
      .of(
        "OpaqueError",
        "CollectionOfErrors",
        "CreateArrayListInput",
        "CreateArrayListOutput",
        "IListOfStrings",
        "ListOfStringsBase",
        "GetElementInput",
        "GetElementOutput",
        "SetElementInput",
        "IndexOutOfBoundsException"
      )
      .map(name -> Path.of(name + ".cs"))
      .collect(Collectors.toSet());
    assertEquals(expectedPaths, codeByPath.keySet());
  }
}
