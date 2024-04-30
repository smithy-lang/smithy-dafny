// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.generator.library.shims.TestServiceShim;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

public class TestJavaLibrary extends JavaLibrary {

  @SuppressWarnings("unused")
  private static final Logger LOGGER = LoggerFactory.getLogger(
    TestJavaLibrary.class
  );

  public TestJavaLibrary(
    Model model,
    ServiceShape serviceShape,
    AwsSdkVersion sdkVersion,
    DafnyVersion dafnyVersion
  ) {
    super(model, serviceShape, sdkVersion, dafnyVersion);
  }

  @Override
  public Map<Path, TokenTree> generate() {
    TestServiceShim shim = new TestServiceShim(this, this.serviceShape);
    return new LinkedHashMap<>(shim.generate());
  }
}
