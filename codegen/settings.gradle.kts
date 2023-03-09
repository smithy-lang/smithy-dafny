rootProject.name = "smithy-dafny"
include(":smithy-dafny-codegen")
include(":smithy-dafny-codegen-test")

pluginManagement {
    repositories {
        mavenLocal()
        mavenCentral()
        gradlePluginPortal()
    }
}
