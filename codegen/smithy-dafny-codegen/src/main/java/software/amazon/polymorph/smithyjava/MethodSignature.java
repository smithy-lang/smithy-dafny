// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.MethodSpec;
import software.amazon.polymorph.utils.ModelUtils;

/**
 * @param method         MethodSpec.Builder that SHOULD have Parameters, Returns, and Modifiers set correctly ( note that
 *                       void or parameterless methods would not have any Returns or Parameters).
 * @param resolvedInput  A ResolvedShapeId representing the input
 * @param resolvedOutput A ResolvedShapeId representing the output
 */
public record MethodSignature(
  MethodSpec.Builder method,
  ModelUtils.ResolvedShapeId resolvedInput,
  ModelUtils.ResolvedShapeId resolvedOutput
) {}
