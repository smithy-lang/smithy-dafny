plugins {
    `java-library`
    `maven-publish`
    id("software.amazon.smithy.gradle.smithy-jar").version("1.1.0")
}

repositories {
    mavenLocal()
    mavenCentral()
}

smithy {
    
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:1.52.0")
    implementation("software.amazon.smithy:smithy-aws-traits:1.52.0")
    implementation("software.amazon.smithy:smithy-rules-engine:1.52.0")
    implementation("software.amazon.smithy.dafny:sqs-model:1.0")
}

