// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleBooleanConfig {}

impl SimpleBooleanConfig {
    pub fn builder() -> SimpleBooleanConfigBuilder {
        SimpleBooleanConfigBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleBooleanConfigBuilder {}

impl SimpleBooleanConfigBuilder {
    /// Creates a new `SimpleBooleanConfigBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<SimpleBooleanConfig, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok(SimpleBooleanConfig {})
    }
}
