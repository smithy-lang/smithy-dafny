// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
import java.io.File
import java.io.FileInputStream
import java.util.Properties

tasks.wrapper {
    gradleVersion = "7.6"
}

plugins {
    `java-library`
    `maven-publish`
}

var props = Properties().apply {
    load(FileInputStream(File(rootProject.rootDir, "../../project.properties")))
}
var dafnyVersion = props.getProperty("dafnyVersion")

group = "simple"
version = "1.0-SNAPSHOT"
description = "CodegenPatches"

java {
    toolchain.languageVersion.set(JavaLanguageVersion.of(8))
    sourceSets["main"].java {
        srcDir("src/main/java")
        srcDir("src/main/dafny-generated")
        srcDir("src/main/smithy-generated")
    }
    sourceSets["test"].java {
        srcDir("src/test/java")
        srcDir("src/test/dafny-generated")
    }
}

repositories {
    mavenCentral()
    mavenLocal()
}

dependencies {
    implementation("org.dafny:DafnyRuntime:${dafnyVersion}")
    implementation("software.amazon.smithy.dafny:conversion:0.1.1")
    implementation("software.amazon.cryptography:StandardLibrary:1.0-SNAPSHOT")
}

publishing {
    publications.create<MavenPublication>("mavenLocal") {
        groupId = group as String?
        artifactId = description
        from(components["java"])
    }
    publications.create<MavenPublication>("maven") {
        groupId = group as String?
        artifactId = description
        from(components["java"])
    }
    repositories { mavenLocal() }
}

tasks.withType<JavaCompile>() {
    options.encoding = "UTF-8"
}

tasks {
    register("runTests", JavaExec::class.java) {
        mainClass.set("TestsFromDafny")
        classpath = sourceSets["test"].runtimeClasspath
    }
}
