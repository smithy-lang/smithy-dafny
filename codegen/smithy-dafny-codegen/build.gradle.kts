description = "Generates Dafny code from Smithy models"
extra["displayName"] = "Smithy :: Dafny :: Codegen"
extra["moduleName"] = "software.amazon.smithy.dafny.codegen"

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

dependencies {
    api("software.amazon.smithy:smithy-codegen-core:$smithyVersion")
    api("software.amazon.smithy:smithy-model:$smithyVersion")
    api("software.amazon.smithy:smithy-rules-engine:$smithyVersion")
    api("software.amazon.smithy:smithy-waiters:$smithyVersion")
    implementation("software.amazon.smithy:smithy-protocol-test-traits:$smithyVersion")
}
