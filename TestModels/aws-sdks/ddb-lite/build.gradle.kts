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

tasks.register("polymorphDafny") {
    dependsOn("build")
    doLast {
        // if needed, specify a projection to use instead
        // default (no projection) is "source"
        val projectionName = "operation-subset"
        copy {
            from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/project.properties"))
            into(".")
        }
        copy {
            from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/Model/"))
            into("model")
        }
        exec {
            // need to adjust the relative import, since we're copying it away
            // the commandLine method does not play nice with sed,
            // so we have to execute it through bash :(
            commandLine("bash", "-c", "sed '4s|../../../../../../../../dafny-dependencies/StandardLibrary/src/Index.dfy|../../../dafny-dependencies/StandardLibrary/src/Index.dfy|' model/ComAmazonawsDynamodbTypes.dfy > model/tmp && mv model/tmp model/ComAmazonawsDynamodbTypes.dfy")
        }
    }
}

tasks.register("polymorphDotnet") {
    dependsOn("build")
    doLast {
        // if needed, specify a projection to use instead
        // default (no projection) is "source"
        val projectionName = "operation-subset"
        copy {
            from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/runtimes/net"))
            into("runtimes/net")
        }
        exec {
            // need to adjust the relative import, since we're copying it away
            // the commandLine method does not play nice with sed,
            // so we have to execute it through bash :(
            commandLine("bash", "-c", "sed 's|../../../../../../../../../dafny-dependencies/StandardLibrary/runtimes/net/STD.csproj|../../../../dafny-dependencies/StandardLibrary/runtimes/net/STD.csproj|' runtimes/net/DynamoDB.csproj > runtimes/net/tmp && mv runtimes/net/tmp runtimes/net/DynamoDB.csproj")
        }
    }
}

tasks.register("polymorphJava") {
    dependsOn("build")
    doLast {
        // if needed, specify a projection to use instead
        // default (no projection) is "source"
        val projectionName = "operation-subset"
        copy {
            from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/runtimes/java"))
            into("runtimes/java")
        }
    }
}

tasks.register("polymorphRust") {
    dependsOn("build")
    doLast {
        // if needed, specify a projection to use instead
        // default (no projection) is "source"
        val projectionName = "operation-subset"
        copy {
            from(layout.buildDirectory.dir("smithyprojections/" + project.name + "/" + projectionName + "/dafny-client-codegen/runtimes/rust/src"))
            into("runtimes/rust/src")
        }
    }
}

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
}
