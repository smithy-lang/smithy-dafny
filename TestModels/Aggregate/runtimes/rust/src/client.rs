// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn crate::r#simple::aggregate::internaldafny::types::ISimpleAggregateClient>
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::types::simple_aggregate_config::SimpleAggregateConfig,
    ) -> Result<Self, BuildError> {
        let inner =
            crate::simple::aggregate::internaldafny::_default::SimpleAggregate(
                &crate::conversions::simple_aggregate_config::_simple_aggregate_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            crate::_Wrappers_Compile::Result::Failure { .. }
        ) {
            // TODO: convert error - the potential types are not modeled!
            return Err(BuildError::other(
                ::aws_smithy_types::error::metadata::ErrorMetadata::builder()
                    .message("Invalid client config")
                    .build(),
            ));
        }
        Ok(Self {
            dafny_client: ::dafny_runtime::upcast_object()(inner.Extract())
        })
    }
}

mod get_aggregate;

mod get_aggregate_known_value_test;
