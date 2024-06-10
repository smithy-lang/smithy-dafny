// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v1;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV1;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV1;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * Generates all the Java Classes needed for
 * Dafny Generated Java to call AWS Services via
 * the AWS SDK for Java V1.
 */
public class JavaAwsSdkV1 extends CodegenSubject {

  // Hack to override Name Resolvers to Aws Sdk V1 specific ones
  // See code comment on ../library/ModelCodegen for details.
  final AwsSdkDafnyV1 dafnyNameResolver;
  final AwsSdkNativeV1 nativeNameResolver;

  /** Public Java Interfaces will go here. */
  public final String packageName;

  private JavaAwsSdkV1(
    ServiceShape serviceShape,
    Model model,
    AwsSdkDafnyV1 dafnyNameResolver,
    AwsSdkNativeV1 nativeNameResolver
  ) {
    super(
      model,
      serviceShape,
      dafnyNameResolver,
      nativeNameResolver,
      AwsSdkVersion.V1
    );
    this.dafnyNameResolver = dafnyNameResolver;
    this.nativeNameResolver = nativeNameResolver;
    this.packageName =
      DafnyNameResolverHelpers.packageNameForNamespace(
        serviceShape.getId().getNamespace()
      );
  }

  public static JavaAwsSdkV1 createJavaAwsSdkV1(
    ServiceShape serviceShape,
    Model model
  ) {
    throw new UnsupportedOperationException(
      "The AWS SDK for Java V1 support has not been tested since we implemented Double support"
    );
    // We need to keep the ball rolling, and I do not have time to refactor & test the AWS-SDK V1 code.
    // For now, I am just marking it as un-supported.
    // If/When we need it (Java Keyrings?), we can resurrect it
    /*final AwsSdkDafnyV1 dafnyNameResolver = new AwsSdkDafnyV1(serviceShape, model);
        final AwsSdkNativeV1 nativeNameResolver = new AwsSdkNativeV1(serviceShape, model);
        return new JavaAwsSdkV1(serviceShape, model, dafnyNameResolver, nativeNameResolver);*/
  }

  public Map<Path, TokenTree> generate() {
    Map<Path, TokenTree> rtn = new HashMap<>();
    ShimV1 shimGenerator = new ShimV1(this);
    ToDafnyAwsV1 toDafnyGenerator = new ToDafnyAwsV1(this);
    ToNativeAwsV1 toNativeGenerator = new ToNativeAwsV1(this);
    rtn.putAll(shimGenerator.generate());
    rtn.putAll(toDafnyGenerator.generate());
    rtn.putAll(toNativeGenerator.generate());
    return rtn;
  }
}
