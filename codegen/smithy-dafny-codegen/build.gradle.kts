// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

description = "Generates Dafny code from Smithy models"
extra["displayName"] = "Smithy :: Dafny :: Codegen"
extra["moduleName"] = "software.amazon.smithy.dafny.codegen"

val smithyVersion: String by project

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
        // For smithy-rust and smithy-python packages
        mavenLocal()
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
    implementation("software.amazon.smithy:smithy-smoke-test-traits:$smithyVersion")
    implementation("software.amazon.smithy:smithy-aws-endpoints:$smithyVersion")

    implementation("org.commonmark:commonmark:0.22.0")

    implementation("com.google.guava:guava:32.0.0-jre")
    implementation("org.slf4j:slf4j-api:1.7.32")
    implementation("org.slf4j:slf4j-simple:1.7.32")

    testImplementation("junit", "junit", "4.13.2")

    // For Smithy-Java
    implementation("software.amazon.awssdk:codegen:2.20.26")
    implementation("com.squareup:javapoet:1.13.0")

    // Smithy-Python
    implementation("software.amazon.smithy.python:smithy-python-codegen:0.1.0")

    // Used for parsing-based tests
    testImplementation("org.antlr:antlr4:4.9.2")

    // Smithy-Rust
    implementation("software.amazon.smithy.rust.codegen:codegen-core:0.1.0")
    implementation("software.amazon.smithy.rust.codegen:codegen-client:0.1.0")
    implementation("org.jetbrains.kotlin:kotlin-stdlib:1.9.20")
}

// TODO: add CodeArtifact publishing logic
