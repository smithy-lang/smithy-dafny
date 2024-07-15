// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

rootProject.name = "smithy-dafny"
include(":smithy-dafny-codegen")
include(":smithy-dafny-codegen-cli")
include(":smithy-dafny-codegen-test")

pluginManagement {
    repositories {
        mavenLocal()
        mavenCentral()
        gradlePluginPortal()
    }
}
