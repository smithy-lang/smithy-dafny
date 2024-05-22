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
}

configure<software.amazon.smithy.gradle.SmithyExtension> {
    // Uncomment this to use a custom projection when building the JAR.
    // projection = "foo"
}

// Uncomment to disable creating a JAR.
tasks["jar"].enabled = false

// TODO: maybe model copying as a separate task,
//       but then we have to figure out how to get it to run
//       after the build is done, which Gradle doesn't like.
//       It's much better to have a task depend on another,
//       but we don't want to overwrite Build..
//tasks.register<Copy>("copyDafnyFiles") {
//    from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/source/dafny-client-codegen/Model/"))
//    into("model")
//    dependsOn(tasks.build)
//}

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
    // default (no projection) is "source"
    val projectionName = "permissions-only"
    copy {
        from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/Model/"))
        into("model")
    }
    copy {
        // ideally we would just copy runtimes itself, 
        // but build plugin calls it "dotnet" and CLI calls it "net"
        from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/runtimes/dotnet"))
        into("runtimes/net")
    }
}
