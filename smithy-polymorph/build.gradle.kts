import java.net.URI
import javax.annotation.Nullable
plugins {
    java
    application
    `maven-publish`
}

group = "software.amazon.polymorph"
version = "0.1.0"

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(17))
    }
}

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
    implementation("dafny.lang:DafnyRuntime:3.10.0")
    implementation("com.squareup:javapoet:1.13.0")
    implementation("software.amazon.dafny:conversion:1.0-SNAPSHOT")
    implementation("software.amazon.smithy:smithy-model:1.21.0")
    implementation("software.amazon.smithy:smithy-codegen-core:[1.0.2,1.1.0[")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:[1.0.2,1.1.0[")
    implementation("software.amazon.smithy:smithy-aws-traits:1.21.0")

    implementation("com.google.guava:guava:30.1-jre")
    implementation("commons-cli:commons-cli:1.4")
    implementation("org.slf4j:slf4j-api:1.7.32")
    implementation("org.slf4j:slf4j-simple:1.7.32")

    testImplementation("junit", "junit", "4.13.2")
    // Used for parsing-based tests
    testImplementation("org.antlr:antlr4:4.9.2")
}

application {
    mainClass.set("software.amazon.polymorph.CodegenCli")
}

publishing {
    publications {
        create<MavenPublication>("smithy-polymorph") {
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
