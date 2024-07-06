// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import org.gradle.api.tasks.testing.logging.TestLogEvent

extra["displayName"] = "Smithy :: Dafny :: Codegen :: Test"
extra["moduleName"] = "software.amazon.smithy.dafny.codegen.test"

tasks["jar"].enabled = false

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

plugins {
    java
    "java-library"
}

tasks.named<Test>("test") {
    // Use JUnit Jupiter for unit tests.
    useJUnitPlatform()
    beforeTest(closureOf<TestDescriptor> {
        logger.lifecycle("Starting: ${this.className}.${this.name} (${this.displayName})")
    })
    afterTest(KotlinClosure2({ descriptor: TestDescriptor, result: TestResult ->
        logger.lifecycle("Finished: ${descriptor.className}.${descriptor.name} (${descriptor.displayName}): $result")
    }))
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation(project(":smithy-dafny-codegen"))
    implementation("software.amazon.smithy:smithy-codegen-core:$smithyVersion")
    testImplementation(platform("org.junit:junit-bom:5.9.3"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    testImplementation("org.hamcrest:hamcrest:2.1")
}
