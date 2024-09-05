// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleDoubleConfig {}

impl SimpleDoubleConfig {
    pub fn builder() -> SimpleDoubleConfigBuilder {
        SimpleDoubleConfigBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleDoubleConfigBuilder {}

impl SimpleDoubleConfigBuilder {
    /// Creates a new `SimpleDoubleConfigBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<SimpleDoubleConfig, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok(SimpleDoubleConfig {})
    }
}
