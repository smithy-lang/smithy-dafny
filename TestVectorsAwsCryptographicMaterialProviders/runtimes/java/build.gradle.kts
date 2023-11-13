import java.io.File
import java.io.FileInputStream
import java.util.Properties
import java.net.URI
import javax.annotation.Nullable

tasks.wrapper {
    gradleVersion = "7.6"
}

plugins {
    `java-library`
    `maven-publish`
}

var props = Properties().apply {
    load(FileInputStream(File(rootProject.rootDir, "../../../project.properties")))
}
var dafnyVersion = props.getProperty("dafnyVersion")

group = "software.amazon.cryptography"
version = "1.0-SNAPSHOT"
description = "TestAwsCryptographicMaterialProviders"

java {
    toolchain.languageVersion.set(JavaLanguageVersion.of(8))
    sourceSets["main"].java {
        srcDir("src/main/java")
        srcDir("src/main/dafny-generated")
        srcDir("src/main/smithy-generated")
    }
    sourceSets["test"].java {
        srcDir("src/test/dafny-generated")
    }
}

var caUrl: URI? = null
@Nullable
val caUrlStr: String? = System.getenv("CODEARTIFACT_REPO_URL")
if (!caUrlStr.isNullOrBlank()) {
    caUrl = URI.create(caUrlStr)
}

var caPassword: String? = null
@Nullable
val caPasswordString: String? = System.getenv("CODEARTIFACT_TOKEN")
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
    implementation("org.dafny:DafnyRuntime:${dafnyVersion}")
    implementation("software.amazon.smithy.dafny:conversion:0.1")
    implementation("software.amazon.cryptography:aws-cryptographic-material-providers:1.0.1")
    implementation(platform("software.amazon.awssdk:bom:2.19.1"))
    implementation("software.amazon.awssdk:dynamodb")
    implementation("software.amazon.awssdk:dynamodb-enhanced")
    implementation("software.amazon.awssdk:kms")
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

tasks.register<JavaExec>("runTests") {
    dependsOn("copyKeysJSON")
    mainClass.set("TestsFromDafny")
    classpath = sourceSets["test"].runtimeClasspath
}

tasks.register<Copy>("copyKeysJSON") {
    from(layout.projectDirectory.file("../../dafny/TestVectorsAwsCryptographicMaterialProviders/test/keys.json"))
    into(layout.projectDirectory.dir("dafny/TestVectorsAwsCryptographicMaterialProviders/test"))
}

