// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
import java.net.URI
import javax.annotation.Nullable

description = "Legacy CLI for generating Dafny code from Smithy models"
extra["displayName"] = "Smithy :: Dafny :: CodegenCLI"
extra["moduleName"] = "software.amazon.smithy.dafny.codegencli"

val smithyVersion: String by project

group = "software.amazon.polymorph"
version = "0.1.0"

var caUrl: URI? = null
@Nullable
val caUrlStr: String? = System.getenv("CODEARTIFACT_URL_SMITHY")
if (!caUrlStr.isNullOrBlank()) {
    caUrl = URI.create(caUrlStr)
}

var caPassword: String? = null
@Nullable
val caPasswordString: String? = System.getenv("CODEARTIFACT_AUTH_TOKEN")
if (!caPasswordString.isNullOrBlank()) {
    caPassword = caPasswordString
}

repositories {
    mavenLocal()
    mavenCentral()
    maybeCodeArtifact(this@Build_gradle, this)
}

dependencies {
    implementation(project(":smithy-dafny-codegen"))

    // For Parsing Smithy Models
    implementation("software.amazon.smithy:smithy-model:$smithyVersion")
    implementation("software.amazon.smithy:smithy-codegen-core:$smithyVersion")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:$smithyVersion")
    implementation("software.amazon.smithy:smithy-aws-traits:$smithyVersion")
    implementation("software.amazon.smithy:smithy-rules-engine:$smithyVersion")
    implementation("software.amazon.smithy:smithy-waiters:$smithyVersion")
    
    implementation("com.google.guava:guava:30.1-jre")
    implementation("commons-cli:commons-cli:1.4")
    implementation("org.slf4j:slf4j-api:1.7.32")
    implementation("org.slf4j:slf4j-simple:1.7.32")

    testImplementation("junit", "junit", "4.13.2")
    // For Smithy-Java
    implementation("software.amazon.awssdk:codegen:2.20.4")
    implementation("com.squareup:javapoet:1.13.0")

    // Used for parsing-based tests
    testImplementation("org.antlr:antlr4:4.9.2")
}

application {
    mainClass.set("software.amazon.polymorph.CodegenCli")
}

publishing {
    publications {
        create<MavenPublication>("smithy-dafny-codegen-cli") {
            from(components["java"])
        }
    }
    repositories{
        mavenLocal()
        maybeCodeArtifact(this@Build_gradle, this)
    }
}


fun maybeCodeArtifact(buildGradle: Build_gradle, repositoryHandler: RepositoryHandler) {
    if (buildGradle.caUrl != null && buildGradle.caPassword != null) {
        repositoryHandler.maven {
            name = "CodeArtifact"
            url = buildGradle.caUrl!!
            credentials {
                username = "aws"
                password = buildGradle.caPassword!!
            }
        }
    }
}
