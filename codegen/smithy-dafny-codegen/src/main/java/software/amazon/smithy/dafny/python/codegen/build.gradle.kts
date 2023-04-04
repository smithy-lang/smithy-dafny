plugins {
    id("software.amazon.smithy").version("0.6.0")
    `maven-publish`
}

allprojects {
    group = "software.amazon.smithy.dafny.python"
    version = "0.1.0"
}

description = "Generates Python code from Smithy models"
extra["displayName"] = "Smithy :: Dafny :: Python :: Codegen"
extra["moduleName"] = "software.amazon.smithy.dafny.python.codegen"

val smithyVersion: String by project

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:1.28.1")
    implementation("software.amazon.smithy:smithy-aws-traits:1.28.1")
    implementation("software.amazon.smithy.python:smithy-python-codegen:0.1.0")
}

publishing {
    publications {
        create<MavenPublication>("maven") {
            groupId = "software.amazon.smithy.dafny.python"
            artifactId = "smithy-dafny-python"
            version = "0.1.0"

            from(components["java"])
        }
    }
}