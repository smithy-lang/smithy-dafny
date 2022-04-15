// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Before;
import org.junit.Test;

import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.validation.ValidatedResult;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

public class NativeWrapperCodegenTest {

    protected Model model;

    protected NativeWrapperCodegen underTest;

    @Before
    public void setup(){
        String rawModel = """
                namespace test.foobar
                resource Baz { operations: [DoSomethingWithInput, DoSomethingWithOutput] }
                operation DoSomethingWithInput { input: DoSomethingInput }
                structure DoSomethingInput {}
                operation DoSomethingWithOutput { output: DoSomethingOutput }
                structure DoSomethingOutput {}
                """;

        this.model = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));

        this.underTest = new NativeWrapperCodegen(
                model,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
    }
}
