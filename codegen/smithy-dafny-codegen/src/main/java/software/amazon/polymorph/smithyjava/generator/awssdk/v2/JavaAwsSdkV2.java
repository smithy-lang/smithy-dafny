// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import com.squareup.javapoet.ClassName;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV2;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * Generates all the Java Classes needed for
 * Dafny Generated Java to call AWS Services via
 * the AWS SDK for Java V2.
 */
public class JavaAwsSdkV2 extends CodegenSubject {

  public static final ClassName BLOB_TO_NATIVE_SDK_BYTES = ClassName.get(
    "software.amazon.awssdk.core",
    "SdkBytes"
  );
  public static final ClassName SDK_BYTES_WRAPPER = ClassName.get(
    "software.amazon.awssdk.core",
    "BytesWrapper"
  );
  public static final MethodReference SDK_BYTES_AS_BYTE_BUFFER =
    new MethodReference(SDK_BYTES_WRAPPER, "asByteBuffer");
  // Hack to override Name Resolvers to Aws Sdk V2 specific ones
  // See code comment on ../library/ModelCodegen for details.
  final AwsSdkDafnyV2 dafnyNameResolver;
  final AwsSdkNativeV2 nativeNameResolver;

  /** Public Java Interfaces will go here. */
  public final String packageName;

  private JavaAwsSdkV2(
    ServiceShape serviceShape,
    Model model,
    AwsSdkDafnyV2 dafnyNameResolver,
    AwsSdkNativeV2 nativeNameResolver
  ) {
    super(
      model,
      serviceShape,
      dafnyNameResolver,
      nativeNameResolver,
      AwsSdkVersion.V2
    );
    this.dafnyNameResolver = dafnyNameResolver;
    this.nativeNameResolver = nativeNameResolver;
    this.packageName = dafnyNameResolver.packageName();
  }

  public static JavaAwsSdkV2 createJavaAwsSdkV2(
    ServiceShape serviceShape,
    Model model,
    DafnyVersion dafnyVersion
  ) {
    final AwsSdkDafnyV2 dafnyNameResolver = new AwsSdkDafnyV2(
      serviceShape,
      model,
      dafnyVersion
    );
    final AwsSdkNativeV2 nativeNameResolver = new AwsSdkNativeV2(
      serviceShape,
      model
    );
    return new JavaAwsSdkV2(
      serviceShape,
      model,
      dafnyNameResolver,
      nativeNameResolver
    );
  }

  public Map<Path, TokenTree> generate() {
    Map<Path, TokenTree> rtn = new HashMap<>();
    ShimV2 shimGenerator = new ShimV2(this);
    ToDafnyAwsV2 toDafnyGenerator = new ToDafnyAwsV2(this);
    ToNativeAwsV2 toNativeGenerator = new ToNativeAwsV2(this);
    rtn.putAll(shimGenerator.generate());
    rtn.putAll(toDafnyGenerator.generate());
    rtn.putAll(toNativeGenerator.generate());
    return rtn;
  }
}
