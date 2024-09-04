// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleEnumConfig {}

impl SimpleEnumConfig {
    pub fn builder() -> SimpleEnumConfigBuilder {
        SimpleEnumConfigBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleEnumConfigBuilder {}

impl SimpleEnumConfigBuilder {
    /// Creates a new `SimpleEnumConfigBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<SimpleEnumConfig, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok(SimpleEnumConfig {})
    }
}
