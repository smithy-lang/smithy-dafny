// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ShapeId;

import java.net.URL;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.*;

public class ServiceCodegenSmokeTest {
    @Test
    public void testCorrectFilesGenerated() {
        final URL modelUrl = Objects.requireNonNull(this.getClass().getClassLoader().getResource("model.smithy"));
        final ModelAssembler assembler = new ModelAssembler();
        ModelUtils.addCustomTraitsToModelAssembler(assembler);
        final Model model = assembler.addImport(modelUrl).assemble().unwrap();

        final ShapeId serviceShapeId = ShapeId.fromParts("polymorph.demo", "StringLists");
        final ServiceCodegen serviceCodegen = new ServiceCodegen(model, serviceShapeId);
        final Map<Path, TokenTree> codeByPath = serviceCodegen.generate();

        final Set<Path> expectedPaths = Stream.of(
                "CreateArrayListInput",
                "CreateArrayListOutput",
                "IListOfStrings",
                "ListOfStringsBase",
                "GetElementInput",
                "GetElementOutput",
                "SetElementInput",
                "StringListsBaseException",
                "IndexOutOfBoundsException"
        ).map(name -> Path.of(name + ".cs")).collect(Collectors.toSet());
        assertEquals(expectedPaths, codeByPath.keySet());
    }
}
