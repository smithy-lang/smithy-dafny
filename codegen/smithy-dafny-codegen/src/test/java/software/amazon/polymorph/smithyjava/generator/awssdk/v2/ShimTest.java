// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static software.amazon.polymorph.smithyjava.generator.awssdk.v2.Constants.DoSomethingOperation;
import static software.amazon.polymorph.smithyjava.generator.awssdk.v2.Constants.DoVoidOperation;
import static software.amazon.polymorph.smithyjava.generator.awssdk.v2.Constants.MockKmsShim;

import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import java.nio.file.Path;
import java.util.Map;
import javax.lang.model.element.Modifier;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.ForEachDafnyTest;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;

public class ShimTest extends ForEachDafnyTest {

  protected ShimV2 underTest;
  protected Model model;
  protected JavaAwsSdkV2 subject;
  protected final DafnyVersion dafnyVersion;

  public ShimTest(DafnyVersion dafnyVersion) {
    this.dafnyVersion = dafnyVersion;
    model = TestSetupUtils.setupLocalModel(ModelConstants.MOCK_KMS);
    subject = TestSetupUtils.setupAwsSdkV2(model, "kms", dafnyVersion);
    underTest = new ShimV2(subject);
  }

  @Test
  public void operation() {
    final MethodSpec actual = underTest
      .operation(ShapeId.fromParts("com.amazonaws.kms", "DoSomething"))
      .orElseThrow(AssertionError::new);
    // By wrapping the actual method spec with a
    // TypeSpec and JavaFile,
    // Javapoet does not fully qualify every type name.
    // Which is nice.
    TypeSpec shim = TypeSpec
      .classBuilder("Shim")
      .addModifiers(Modifier.PUBLIC, Modifier.FINAL)
      .addMethod(actual)
      .build();

    JavaFile javaFile = JavaFile.builder(subject.packageName, shim).build();
    final String actualString = javaFile.toString();
    assertTrue(
      ("""
        Expected actual to contain excepted.
        Actual:
        %s

        Expected:
        %s""").formatted(actualString, DoSomethingOperation(dafnyVersion)),
      actualString.contains(DoSomethingOperation(dafnyVersion))
    );
  }

  @Test
  public void operationVoid() {
    final MethodSpec actual = underTest
      .operation(ShapeId.fromParts("com.amazonaws.kms", "DoVoid"))
      .orElseThrow(AssertionError::new);
    // By wrapping the actual method spec with a
    // TypeSpec and JavaFile,
    // Javapoet does not fully qualify every type name.
    // Which is nice.
    TypeSpec shim = TypeSpec
      .classBuilder("Shim")
      .addModifiers(Modifier.PUBLIC, Modifier.FINAL)
      .addMethod(actual)
      .build();

    JavaFile javaFile = JavaFile.builder(subject.packageName, shim).build();
    final String actualString = javaFile.toString();
    assertTrue(
      ("""
        Expected actual to contain excepted.
        Actual:
        %s

        Expected:
        %s""").formatted(actualString, DoVoidOperation(dafnyVersion)),
      actualString.contains(DoVoidOperation(dafnyVersion))
    );
  }

  @Test
  public void generate() {
    final Map<Path, TokenTree> actual = underTest.generate();
    // TODO: refactor so that Shim is written as
    // com.amazonaws.encryptionsdk.kms.Shim.java
    final Path expectedPath = Path.of(
      "software/amazon/cryptography/services/kms/internaldafny/Shim.java"
    );
    Path[] temp = new Path[1];
    final Path actualPath = actual.keySet().toArray(temp)[0];
    assertEquals(expectedPath, actualPath);
    final String actualSource = actual.get(actualPath).toString();
    final String mockKmsShim = MockKmsShim(dafnyVersion);
    Tokenizer.tokenizeAndAssertEqual(mockKmsShim, actualSource);
  }
}
