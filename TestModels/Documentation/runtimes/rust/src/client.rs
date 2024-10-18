// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
/// A service that supports the operation of getting things.
///
/// This is still part of the same documentation trait
/// even though it's separated.
///
/// It's also important to make sure we don't incorrectly
/// reject multiline plaintext comments
/// because we incorrectly think newlines are CommonMark
/// syntax.
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn crate::r#simple::documentation::internaldafny::types::ISimpleDocumentationClient>
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::types::simple_documentation_config::SimpleDocumentationConfig,
    ) -> Result<Self, crate::types::error::Error> {
        let inner =
            crate::simple::documentation::internaldafny::_default::SimpleDocumentation(
                &crate::conversions::simple_documentation_config::_simple_documentation_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            crate::_Wrappers_Compile::Result::Failure { .. }
        ) {
            return Err(crate::conversions::error::from_dafny(inner.as_ref().error().clone()));
        }
        Ok(Self {
            dafny_client: ::dafny_runtime::upcast_object()(inner.Extract())
        })
    }
}

mod get_thing;
