plugins {
    id("software.amazon.smithy").version("0.6.0")
}

buildscript {
    repositories {
        mavenLocal()
        mavenCentral()
    }
    dependencies {
        classpath("software.amazon.smithy:smithy-aws-traits:1.29.0")
    }
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("software.amazon.smithy:smithy-model:1.29.0")

    // Any dependencies that the projected model needs must be (re)declared
    // here. For example, let's assume that the smithy-aws-traits package is
    // needed in the projected model too.
    implementation("software.amazon.smithy:smithy-aws-traits:1.29.0")
}