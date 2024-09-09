// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient>
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::types::simple_errors_config::SimpleErrorsConfig,
    ) -> Result<Self, crate::types::error::Error> {
        let inner =
            crate::simple::errors::internaldafny::_default::SimpleErrors(
                &crate::conversions::simple_errors_config::_simple_errors_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            crate::_Wrappers_Compile::Result::Failure { .. }
        ) {
            return Err(crate::conversions::error::from_dafny(inner.error));
        }
        Ok(Self {
            dafny_client: ::dafny_runtime::upcast_object()(inner.Extract())
        })
    }
}

mod always_error;

mod always_multiple_errors;

mod always_native_error;
