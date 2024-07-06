// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

rootProject.name = "smithy-dafny"
include(":smithy-dafny-codegen")
include(":smithy-dafny-codegen-cli")
// TODO: Once Smithy-Python is published to Maven, and we do not rely on a fork, use that
include(":smithy-python-codegen")
project(":smithy-python-codegen").projectDir = file("./smithy-dafny-codegen-modules/smithy-python/codegen/smithy-python-codegen")
include(":smithy-dafny-codegen-test")

pluginManagement {
    repositories {
        mavenLocal()
        mavenCentral()
        gradlePluginPortal()
    }
}
