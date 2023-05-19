// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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

sourceSets {
    test {
        resources {
            srcDirs("../TestModels")
        }
    }
}

tasks.named<Test>("test") {
    // Use JUnit Jupiter for unit tests.
    useJUnitPlatform()

    maxParallelForks = Runtime.getRuntime().availableProcessors() / 2
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation(project(":smithy-dafny-codegen"))
    testImplementation(platform("org.junit:junit-bom:5.9.3"))
    testImplementation("org.junit.jupiter:junit-jupiter")
}
