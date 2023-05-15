import java.net.URI
import javax.annotation.Nullable

plugins {
    `java-library`
    `maven-publish`
}
description = "Convert Native Java Types to Dafny Runtime Types and vice versa"
group = "software.amazon.smithy.dafny"
var artifactId = "conversion"
version = "1.0-SNAPSHOT"

var moduleName = "%s.%s".format(group, artifactId)
var displayName = "Smithy :: Dafny :: Conversion"

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
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

publishing {
    publications {
        create<MavenPublication>("conversion") {
            groupId = "software.amazon.dafny"
            artifactId = "conversion"
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
