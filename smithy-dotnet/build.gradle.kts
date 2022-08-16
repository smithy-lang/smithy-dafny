plugins {
    java
    application
}

group = "software.amazon.polymorph"
version = "0.1.0"

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(16))
    }
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
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
