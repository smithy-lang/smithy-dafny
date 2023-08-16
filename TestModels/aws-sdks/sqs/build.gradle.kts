// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

plugins {
    id("software.amazon.smithy").version("0.6.0")
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:1.28.0")
    implementation("software.amazon.smithy:smithy-aws-traits:1.28.0")
    implementation("software.amazon.smithy:smithy-rules-engine:1.28.0")

    // Must be built and published to the local Maven repo
    implementation("software.amazon.smithy.dafny:smithy-dafny-codegen:0.1.0")
    implementation("software.amazon.smithy.python:smithy-python-codegen:0.1.0")
}

configure<software.amazon.smithy.gradle.SmithyExtension> {
    // Uncomment this to use a custom projection when building the JAR.
    // projection = "foo"
}

// Uncomment to disable creating a JAR.
tasks["jar"].enabled = false

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
}
