import java.net.URI
import javax.annotation.Nullable

plugins {
    `java-library`
    `maven-publish`
    `signing`
    id("com.github.johnrengelman.shadow") version "7.1.2"
    id("io.github.gradle-nexus.publish-plugin") version "1.3.0"
}

group = "software.amazon.cryptography"
version = "1.0.0-preview-2"
description = "AWS Cryptographic Material Providers Library"

java {
    toolchain.languageVersion.set(JavaLanguageVersion.of(8))
    sourceSets["main"].java {
        mainSourceSet()
    }
    sourceSets["test"].java {
        srcDir("src/test")
    }
    withJavadocJar()
    withSourcesJar()
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
    if (caUrl != null && caPassword != null) {
        maven {
            name = "CodeArtifact"
            url = caUrl!!
            credentials {
                username = "aws"
                password = caPassword!!
            }
        }
    }
}

dependencies {
    // generated dependencies
    implementation("software.amazon.cryptography:StandardLibrary:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:AwsCryptographyPrimitives:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:ComAmazonawsKms:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:ComAmazonawsDynamodb:1.0-SNAPSHOT")

    // Dafny dependencies
    implementation("org.dafny:DafnyRuntime:4.1.0")
    implementation("software.amazon.smithy.dafny:conversion:0.1")

    // sdk dependencies
    implementation(platform("software.amazon.awssdk:bom:2.19.1"))
    implementation("software.amazon.awssdk:dynamodb")
    implementation("software.amazon.awssdk:dynamodb-enhanced")
    implementation("software.amazon.awssdk:kms")

    // https://mvnrepository.com/artifact/org.testng/testng
    testImplementation("org.testng:testng:7.5")
}

publishing {
    publications.create<MavenPublication>("mavenLocal") {
        groupId = "software.amazon.cryptography"
        artifactId = "aws-cryptographic-material-providers"
        artifact(tasks["shadowJar"])
        artifact(tasks["javadocJar"])
        artifact(tasks["sourcesJar"])

        // Since we ship the MPL bundled with our generated dependencies they should not be included in the generated pom.xml
        // however; we also use additional dependencies runtime dependencies that are needed in order to properly run the mpl.
        // When you bundle a shadow jar you don't need to include any dependencies in the pom.xml since everything is on the jar, but since
        // we are selective so we have to "manually" write our own pom file.
        pom.withXml {
            var dependencyManagementNode = asNode().appendNode("dependencyManagement").appendNode("dependencies").appendNode("dependency")
            var sdkPomDependency = configurations.implementation.get().dependencies.find { dependency ->  dependency.group.equals("software.amazon.awssdk") && dependency.name.equals("bom") }
            if (sdkPomDependency != null) {
                dependencyManagementNode.appendNode("groupId", sdkPomDependency.group)
                dependencyManagementNode.appendNode("artifactId", sdkPomDependency.name)
                dependencyManagementNode.appendNode("version", sdkPomDependency.version)
                dependencyManagementNode.appendNode("type", "pom")
                dependencyManagementNode.appendNode("scope", "import")
            }

            var dependenciesNode = asNode().appendNode("dependencies")
            configurations.implementation.get().dependencies.forEach {
                // we don't want to include generated dependencies
                if (!(it.name.equals("StandardLibrary") ||
                                it.name.equals("AwsCryptographyPrimitives") ||
                                it.name.equals("ComAmazonawsKms") ||
                                it.name.equals("ComAmazonawsDynamodb") ||
                                it.name.equals("bom"))
                ) {
                    var dependencyNode = dependenciesNode.appendNode("dependency")
                    dependencyNode.appendNode("groupId", it.group)
                    dependencyNode.appendNode("artifactId", it.name)
                    if (!it.version.isNullOrEmpty()) {
                        dependencyNode.appendNode("version", it.version)
                    }
                    dependencyNode.appendNode("scope", "runtime")
                }
            }
        }

        // Include extra information in the POMs.
        afterEvaluate {
            pom {
                name.set("AWS Cryptographic Material Providers Library")
                description.set("The AWS Cryptographic Material Providers Library for Java")
                url.set("https://github.com/aws/aws-cryptographic-material-providers-library-java")
                licenses {
                    license {
                        name.set("Apache License 2.0")
                        url.set("http://www.apache.org/licenses/LICENSE-2.0.txt")
                        distribution.set("repo")
                    }
                }
                developers {
                    developer {
                        id.set("amazonwebservices")
                        organization.set("Amazon Web Services")
                        organizationUrl.set("https://aws.amazon.com")
                        roles.add("developer")
                    }
                }
                scm {
                    url.set("https://github.com/aws/aws-cryptographic-material-providers-library-java.git")
                }
            }
        }
    }

    publications.create<MavenPublication>("maven") {
        groupId = "software.amazon.cryptography"
        artifactId = "aws-cryptographic-material-providers"
        artifact(tasks["shadowJar"])
        artifact(tasks["javadocJar"])
        artifact(tasks["sourcesJar"])

        // Since we ship the MPL bundled with our generated dependencies they should not be included in the generated pom.xml
        // however; we also use additional dependencies runtime dependencies that are needed in order to properly run the mpl.
        // When you bundle a shadow jar you don't need to include any dependencies in the pom.xml since everything is on the jar, but since
        // we are selective so we have to "manually" write our own pom file.
        pom.withXml {
            var dependencyManagementNode = asNode().appendNode("dependencyManagement").appendNode("dependencies").appendNode("dependency")
            var sdkPomDependency = configurations.implementation.get().dependencies.find { dependency ->  dependency.group.equals("software.amazon.awssdk") && dependency.name.equals("bom") }
            if (sdkPomDependency != null) {
                dependencyManagementNode.appendNode("groupId", sdkPomDependency.group)
                dependencyManagementNode.appendNode("artifactId", sdkPomDependency.name)
                dependencyManagementNode.appendNode("version", sdkPomDependency.version)
                dependencyManagementNode.appendNode("type", "pom")
                dependencyManagementNode.appendNode("scope", "import")
            }

            var dependenciesNode = asNode().appendNode("dependencies")
            configurations.implementation.get().dependencies.forEach {
                // we don't want to include generated dependencies
                if (!(it.name.equals("StandardLibrary") ||
                                it.name.equals("AwsCryptographyPrimitives") ||
                                it.name.equals("ComAmazonawsKms") ||
                                it.name.equals("ComAmazonawsDynamodb") ||
                                it.name.equals("bom"))
                ) {
                    var dependencyNode = dependenciesNode.appendNode("dependency")
                    dependencyNode.appendNode("groupId", it.group)
                    dependencyNode.appendNode("artifactId", it.name)
                    if (!it.version.isNullOrEmpty()) {
                        dependencyNode.appendNode("version", it.version)
                    }
                    dependencyNode.appendNode("scope", "runtime")
                }
            }
        }

        // Include extra information in the POMs.
        afterEvaluate {
            pom {
                name.set("AWS Cryptographic Material Providers Library")
                description.set("The AWS Cryptographic Material Providers Library for Java")
                url.set("https://github.com/aws/aws-cryptographic-material-providers-library-java")
                licenses {
                    license {
                        name.set("Apache License 2.0")
                        url.set("http://www.apache.org/licenses/LICENSE-2.0.txt")
                        distribution.set("repo")
                    }
                }
                developers {
                    developer {
                        id.set("amazonwebservices")
                        organization.set("Amazon Web Services")
                        organizationUrl.set("https://aws.amazon.com")
                        roles.add("developer")
                    }
                }
                scm {
                    url.set("https://github.com/aws/aws-cryptographic-material-providers-library-java.git")
                }
            }
        }
    }

    repositories {
        mavenLocal()
        maven {
            name = "PublishToCodeArtifactStaging"
            url = URI.create("https://crypto-tools-internal-587316601012.d.codeartifact.us-east-1.amazonaws.com/maven/java-mpl-staging/")
            credentials {
                username = "aws"
                password = System.getenv("CODEARTIFACT_TOKEN")
            }
        }
    }
}

tasks.withType<JavaCompile>() {
    options.encoding = "UTF-8"
}


tasks.withType<Jar>() {
    // to compile a sources jar we need a strategy on how to deal with duplicates;
    // we choose to include duplicate classes.
    duplicatesStrategy = DuplicatesStrategy.INCLUDE
}

tasks {
    register("runTests", JavaExec::class.java) {
        mainClass.set("TestsFromDafny")
        classpath = sourceSets["test"].runtimeClasspath
    }
}

tasks.jar {
    enabled = false
}

tasks.javadoc {
    options {
        (this as CoreJavadocOptions).addStringOption("Xdoclint:none", "-quiet")
    }
    exclude("src/main/dafny-generated")
}

tasks.build {
    dependsOn(tasks.shadowJar)
}

tasks.shadowJar {
    mergeServiceFiles()
    archiveClassifier.set("")

    dependencies {
        include(dependency("software.amazon.cryptography:StandardLibrary:1.0-SNAPSHOT"))
        include(dependency("software.amazon.cryptography:AwsCryptographyPrimitives:1.0-SNAPSHOT"))
        include(dependency("software.amazon.cryptography:ComAmazonawsKms:1.0-SNAPSHOT"))
        include(dependency("software.amazon.cryptography:ComAmazonawsDynamodb:1.0-SNAPSHOT"))
    }

    configurations {
        runtimeClasspath {
            dependencies {
                // We want to package this version of BC since it is the one the Primitives depends on.
                // These dependencies need to remain in sync with one another.
               include(dependency("org.bouncycastle:bcprov-jdk18on:1.72"))
            }
        }
        sourceSets["main"].java {
            mainSourceSet()
        }
    }
}

nexusPublishing {
    // We are using the nexusPublishing plugin since it is recommended by Sonatype Gradle Project configurations
    // and it is easy to supply the creds we need to deploy
    // https://github.com/gradle-nexus/publish-plugin/
    repositories {
        sonatype {
            nexusUrl.set(uri("https://aws.oss.sonatype.org/service/local/"))
            snapshotRepositoryUrl.set(uri("https://aws.oss.sonatype.org/content/repositories/snapshots/"))
            username.set(System.getenv("SONA_USERNAME"))
            password.set(System.getenv("SONA_PASSWORD"))
        }
    }
}

signing {
    useGpgCmd()

    // Dynamically set these properties
    project.ext.set("signing.gnupg.executable", "gpg")
    project.ext.set("signing.gnupg.useLegacyGpg" , "true")
    project.ext.set("signing.gnupg.homeDir", System.getenv("HOME") + "/.gnupg/")
    project.ext.set("signing.gnupg.optionsFile", System.getenv("HOME") + "/.gnupg/gpg.conf")
    project.ext.set("signing.gnupg.keyName", System.getenv("GPG_KEY"))
    project.ext.set("signing.gnupg.passphrase", System.getenv("GPG_PASS"))

    // Signing is required if building a release version and if we're going to publish it.
    // Otherwise if doing a maven publication we will sign
    setRequired({
        gradle.getTaskGraph().hasTask("publish")
    })
    sign(publishing.publications["maven"])
}

fun SourceDirectorySet.mainSourceSet() {
    srcDir("src/main/java")
    srcDir("src/main/dafny-generated")
    srcDir("src/main/smithy-generated")
}


tasks.test {
    useTestNG()

    // This will show System.out.println statements
    testLogging.showStandardStreams = true

    testLogging {
        lifecycle {
            events = mutableSetOf(org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED, org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED, org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED)
            exceptionFormat = org.gradle.api.tasks.testing.logging.TestExceptionFormat.FULL
            showExceptions = true
            showCauses = true
            showStackTraces = true
            showStandardStreams = true
        }
        info.events = lifecycle.events
        info.exceptionFormat = lifecycle.exceptionFormat
    }

    // See https://github.com/gradle/kotlin-dsl/issues/836
    addTestListener(object : TestListener {
        override fun beforeSuite(suite: TestDescriptor) {}
        override fun beforeTest(testDescriptor: TestDescriptor) {}
        override fun afterTest(testDescriptor: TestDescriptor, result: TestResult) {}

        override fun afterSuite(suite: TestDescriptor, result: TestResult) {
            if (suite.parent == null) { // root suite
                logger.lifecycle("----")
                logger.lifecycle("Test result: ${result.resultType}")
                logger.lifecycle("Test summary: ${result.testCount} tests, " +
                        "${result.successfulTestCount} succeeded, " +
                        "${result.failedTestCount} failed, " +
                        "${result.skippedTestCount} skipped")
            }
        }
    })
}