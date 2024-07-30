// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import java.util.regex.Pattern.compile

description = "Generates Dafny code from Smithy models"
extra["displayName"] = "Smithy :: Dafny :: Codegen"
extra["moduleName"] = "software.amazon.smithy.dafny.codegen"

val smithyVersion: String by project

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:$smithyVersion")
    implementation("software.amazon.smithy:smithy-codegen-core:$smithyVersion")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:$smithyVersion")
    implementation("software.amazon.smithy:smithy-aws-traits:$smithyVersion")
    implementation("software.amazon.smithy:smithy-rules-engine:$smithyVersion")
    implementation("software.amazon.smithy:smithy-waiters:$smithyVersion")
    // Using a hard coded version here because this package didn't exist until 1.40.0,
    // but upgrading $smithyVersion ends up breaking the sqs-via-cli test model
    // because the SQS model isn't actually valid, and newer versions of Smithy crash on it.
    // We also can't yet update the SQS model because newer versions use Smithy 2.0 enum shapes,
    // which we don't yet support for .NET.
    // See https://github.com/smithy-lang/smithy-dafny/issues/184#issuecomment-2105109715
    implementation("software.amazon.smithy:smithy-smoke-test-traits:1.49.0")

    implementation("org.commonmark:commonmark:0.22.0")

    implementation("com.google.guava:guava:30.1-jre")
    implementation("org.slf4j:slf4j-api:1.7.32")
    implementation("org.slf4j:slf4j-simple:1.7.32")

    testImplementation("junit", "junit", "4.13.2")

    // For Smithy-Java
    implementation("software.amazon.awssdk:codegen:2.20.26")
    implementation("com.squareup:javapoet:1.13.0")

    // Used for parsing-based tests
    testImplementation("org.antlr:antlr4:4.9.2")
}

// TODO: add CodeArtifact publishing logic
