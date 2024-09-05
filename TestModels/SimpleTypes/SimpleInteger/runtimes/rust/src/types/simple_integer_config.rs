// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleIntegerConfig {}

impl SimpleIntegerConfig {
    pub fn builder() -> SimpleIntegerConfigBuilder {
        SimpleIntegerConfigBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleIntegerConfigBuilder {}

impl SimpleIntegerConfigBuilder {
    /// Creates a new `SimpleIntegerConfigBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<SimpleIntegerConfig, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok(SimpleIntegerConfig {})
    }
}
