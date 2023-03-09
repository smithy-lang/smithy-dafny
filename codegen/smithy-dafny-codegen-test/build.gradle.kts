extra["displayName"] = "Smithy :: Dafny :: Codegen :: Test"
extra["moduleName"] = "software.amazon.smithy.dafny.codegen.test"

tasks["jar"].enabled = false

val smithyVersion: String by project

buildscript {
    val smithyVersion: String by project

    repositories {
        mavenCentral()
    }
    dependencies {
        "classpath"("software.amazon.smithy:smithy-cli:$smithyVersion")
    }
}

plugins {
    val smithyGradleVersion: String by project

    id("software.amazon.smithy").version(smithyGradleVersion)
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation(project(":smithy-dafny-codegen"))
    implementation("software.amazon.smithy:smithy-waiters:$smithyVersion")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:$smithyVersion")
}
