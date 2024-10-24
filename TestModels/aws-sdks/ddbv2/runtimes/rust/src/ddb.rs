// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(nonstandard_style)]
#![deny(clippy::all)]

use std::sync::LazyLock;

static DAFNY_TOKIO_RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap()
});

#[allow(non_snake_case)]
impl crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::_default {
    pub fn DynamoDBClient() -> ::std::rc::Rc<
  crate::r#_Wrappers_Compile::Result<
    ::dafny_runtime::Object<dyn crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>,
    ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
    >
    >{
        let shared_config = match tokio::runtime::Handle::try_current() {
            Ok(curr) => tokio::task::block_in_place(|| {
                curr.block_on(async {
                    aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()).await
                })
            }),
            Err(_) => DAFNY_TOKIO_RUNTIME.block_on(aws_config::load_defaults(
                aws_config::BehaviorVersion::v2024_03_28(),
            )),
        };
        let inner = aws_sdk_dynamodb::Client::new(&shared_config);
        let client = crate::client::Client { inner };
        let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
        std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::Success {
            value: dafny_client,
        })
    }
}
