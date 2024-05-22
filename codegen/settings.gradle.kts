// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

rootProject.name = "smithy-dafny"
include(":smithy-dafny-codegen")
include(":smithy-dafny-codegen-cli")
//include(":smithy-dafny-codegen-test")
include(":smithy-rust-client-codegen")
project(":smithy-rust-client-codegen").projectDir = file("../smithy-dafny-codegen-modules/smithy-rs/codegen-client")

pluginManagement {
    repositories {
        mavenLocal()
        mavenCentral()
        gradlePluginPortal()
    }
}
