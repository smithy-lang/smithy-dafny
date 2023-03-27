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
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
}

dependencies {
    api("software.amazon.smithy:smithy-codegen-core:$smithyVersion")
    api("software.amazon.smithy:smithy-model:$smithyVersion")
    api("software.amazon.smithy:smithy-rules-engine:$smithyVersion")
    api("software.amazon.smithy:smithy-waiters:$smithyVersion")

    implementation("com.google.guava:guava:30.1-jre")
    implementation("commons-cli:commons-cli:1.4")
    implementation("org.slf4j:slf4j-api:1.7.32")
    implementation("org.slf4j:slf4j-simple:1.7.32")
    implementation("software.amazon.smithy:smithy-aws-traits:1.28.1")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:$smithyVersion")

    testImplementation("junit", "junit", "4.13.2")

    // For Smithy-Java
    implementation("software.amazon.awssdk:codegen:2.20.26")
    implementation("dafny.lang:DafnyRuntime:3.10.0")
    implementation("com.squareup:javapoet:1.13.0")
    implementation("software.amazon.dafny:conversion:1.0-SNAPSHOT")

    // Used for parsing-based tests
    testImplementation("org.antlr:antlr4:4.9.2")
}

// TODO: add CodeArtifact publishing logic
