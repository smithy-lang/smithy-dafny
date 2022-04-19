// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Before;

import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

public class NativeWrapperCodegenTest {

    protected Model model;

    protected DotNetNameResolver nameResolver;

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
        this.nameResolver = getNameResolver(model, SERVICE_SHAPE_ID);
    }

    @SuppressWarnings("SameParameterValue")
    protected static DotNetNameResolver getNameResolver(Model model, ShapeId shapeId) {
        return new DotNetNameResolver(model,
                model.expectShape(shapeId, ServiceShape.class));
    }
}
