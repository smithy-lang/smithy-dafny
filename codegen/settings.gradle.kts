// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

rootProject.name = "smithy-dafny"
include(":smithy-dafny-codegen")
include(":smithy-dafny-codegen-cli")
include(":smithy-python-codegen")
project(":smithy-python-codegen").projectDir = file("../submodules/smithy-python/codegen/smithy-python-codegen")

pluginManagement {
    repositories {
        mavenLocal()
        gradlePluginPortal()
    }
}
