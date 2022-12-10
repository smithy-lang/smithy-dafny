import java.net.URI
import javax.annotation.Nullable

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
    implementation("dafny.lang:DafnyRuntime:3.9.0")
    testImplementation("junit", "junit", "4.13.2")
}

var caUrl: URI? = null
@Nullable
val caUrlStr: String? = System.getenv("CODEARTIFACT_URL_CONVERSION")
if (!caUrlStr.isNullOrBlank()) {
    caUrl = URI.create(caUrlStr)
}

var caPassword: String? = null
@Nullable
val caPasswordString: String? = System.getenv("CODEARTIFACT_AUTH_TOKEN")
if (!caPasswordString.isNullOrBlank()) {
    caPassword = caPasswordString
}


publishing {
    publications {
        create<MavenPublication>("conversion") {
            groupId = "software.amazon.dafny"
            artifactId = "conversion"
            from(components["java"])
        }
    }
    repositories{
        mavenLocal()
        if (caUrl != null && caPassword != null) {
            maven {
                name = "CodeArtifact"
                url = caUrl!!
                credentials {
                    username = "aws"
                    password = caPassword!!
                }
            }
        }
    }
}
