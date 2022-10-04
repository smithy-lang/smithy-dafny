plugins {
    java
    `maven-publish`
}

group = "software.amazon.dafny"
version = "1.0-SNAPSHOT"

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

repositories {
    mavenCentral()
    mavenLocal()
}

dependencies {
    implementation("dafny.lang:DafnyRuntime:3.8.1")
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
    repositories{ mavenLocal() }
}
