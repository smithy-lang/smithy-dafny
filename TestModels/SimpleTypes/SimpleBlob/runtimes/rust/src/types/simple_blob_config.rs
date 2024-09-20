// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleBlobConfig {}

impl SimpleBlobConfig {
    pub fn builder() -> SimpleBlobConfigBuilder {
        SimpleBlobConfigBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleBlobConfigBuilder {}

impl SimpleBlobConfigBuilder {
    /// Creates a new `SimpleBlobConfigBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<SimpleBlobConfig, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok(SimpleBlobConfig {})
    }
}
