tasks.wrapper {
    gradleVersion = "7.6"
}

plugins {
    `java-library`
    `maven-publish`
}

group = "simple"
version = "1.0-SNAPSHOT"
description = "LocalService"

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
    implementation("org.dafny:DafnyRuntime:4.1.0")
    implementation("software.amazon.smithy.dafny:conversion:1.0-SNAPSHOT")
    implementation("software.amazon.cryptography:StandardLibrary:1.0-SNAPSHOT")
}

publishing {
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
