// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator;

import java.nio.file.Path;
import java.util.Map;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * The Subject of code generation.
 * Provides generators access to Name Resolvers, Model, and Service Shape
 * specific to the subject.
 * Extensions should customize name resolvers.
 */
public abstract class CodegenSubject {

  public final Dafny dafnyNameResolver;
  public final Native nativeNameResolver;
  public final Model model;
  public final ServiceShape serviceShape;
  public final AwsSdkVersion sdkVersion;

  protected CodegenSubject(
    Model model,
    ServiceShape serviceShape,
    Dafny dafnyNameResolver,
    Native nativeNameResolver,
    AwsSdkVersion sdkVersion
  ) {
    this.model = model;
    this.serviceShape = serviceShape;
    this.dafnyNameResolver = dafnyNameResolver;
    this.nativeNameResolver = nativeNameResolver;
    this.sdkVersion = sdkVersion;
  }

  /**
   * Generates Java Code for the Subject.
   */
  public abstract Map<Path, TokenTree> generate();

  public enum AwsSdkVersion {
    V1,
    V2,
  }
}
