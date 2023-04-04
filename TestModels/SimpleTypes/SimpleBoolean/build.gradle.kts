plugins {
    id("software.amazon.smithy").version("0.6.0")
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:1.28.1")
    implementation("software.amazon.smithy:smithy-aws-traits:1.28.1")
    implementation("software.amazon.smithy.dafny.python:smithy-dafny-python:0.1.0")
}