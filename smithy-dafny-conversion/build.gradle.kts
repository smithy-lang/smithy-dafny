// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
import java.net.URI
import javax.annotation.Nullable

plugins {
    `java-library`
    `maven-publish`
    signing
    id("io.github.gradle-nexus.publish-plugin") version "1.1.0"
}
description = "Convert Native Java Types to Dafny Runtime Types and vice versa"
group = "software.amazon.smithy.dafny"
var artifactId = "conversion"
version = "0.1.1"

var moduleName = "%s.%s".format(group, artifactId)
var displayName = "Smithy :: Dafny :: Conversion"

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

var caUrl: URI? = null
@Nullable
val caUrlStr: String? = System.getenv("CODEARTIFACT_URL_JAVA_CONVERSION")
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
    mavenCentral()
    mavenLocal()
    maybeCodeArtifact(this@Build_gradle, this)
}

dependencies {
    implementation("org.dafny:DafnyRuntime:4.1.0")
    testImplementation("junit", "junit", "4.13.2")
}

tasks.register<Jar>("javadocJar") {
    from(tasks.javadoc)
    archiveClassifier.set("javadoc")
}

tasks.register<Jar>("sourcesJar") {
    from(sourceSets.main.get().allJava)
    archiveClassifier.set("sources")
    inputs.property("moduleName", moduleName)
    manifest {
        attributes["Automatic-Module-Name"] = moduleName
    }
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            groupId = group.toString()
            artifactId = this@Build_gradle.artifactId
            // Ship the source and javadoc jars.
            from(components["java"])
            artifact(tasks["sourcesJar"])
            artifact(tasks["javadocJar"])

            // Include extra information in the POMs.
            afterEvaluate {
                pom {
                    name.set("Smithy :: Dafny :: Conversion")
                    description.set("Convert Native Java Types to Dafny Runtime Types and vice versa")
                    url.set("https://github.com/smithy-lang/smithy")
                    licenses {
                        license {
                            name.set("Apache License 2.0")
                            url.set("http://www.apache.org/licenses/LICENSE-2.0.txt")
                            distribution.set("repo")
                        }
                    }
                    developers {
                        developer {
                            id.set("smithy")
                            name.set("Smithy")
                            organization.set("Amazon Web Services")
                            organizationUrl.set("https://aws.amazon.com")
                            roles.add("developer")
                        }
                    }
                    scm {
                        url.set("https://github.com/smithy-lang/smithy.git")
                    }
                }
            }
        }
        repositories {
            mavenLocal()
            maybeCodeArtifact(this@Build_gradle, this)
        }
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

signing {
    // Signing is required if building a release version and if we're going to publish it.
    // Otherwise, signing will only occur if signatory credentials are configured.
    setRequired({
         gradle.getTaskGraph().hasTask("publish") 
    })

    sign(publishing.publications["mavenJava"])
}

nexusPublishing {
    repositories {
        sonatype {
            nexusUrl.set(uri("https://aws.oss.sonatype.org/service/local/"))
            snapshotRepositoryUrl.set(uri("https://aws.oss.sonatype.org/content/repositories/snapshots/"))
        }
    }
}
