// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import software.amazon.smithy.model.shapes.Shape;

public interface ShapeGenerator<T extends Shape> {
    public void generate(T shape);
}
