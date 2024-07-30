// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithypython.localservice.extensions;

import software.amazon.polymorph.smithypython.localservice.ConstraintUtils;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.UnionGenerator;

import java.util.Set;

/**
 * Extend Smithy-Python's UnionGenerator to write Constraint traits.
 */
public class DafnyPythonLocalServiceUnionGenerator extends UnionGenerator {

    public DafnyPythonLocalServiceUnionGenerator(Model model, SymbolProvider symbolProvider, PythonWriter writer, UnionShape shape, Set<Shape> recursiveShapes) {
        super(model, symbolProvider, writer, shape, recursiveShapes);
    }

    @Override
    protected void writeInitMethodConstraintsChecksForMember(MemberShape member, String memberName) {
        // Smithy-Python UnionGenerator hardcodes "value" as union values
        ConstraintUtils.writeInitMethodConstraintsChecksForMember(writer, model, member, "value");
    }
}

