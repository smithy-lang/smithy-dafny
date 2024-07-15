// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<
        dyn crate::implementation_from_dafny::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
    >,
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::types::simple_union_config::SimpleUnionConfig,
    ) -> Result<Self, BuildError> {
        let inner = crate::implementation_from_dafny::_simple_dunion_dinternaldafny::_default::SimpleUnion(
            &crate::conversions::simple_union_config::_simple_union_config::to_dafny(conf),
        );
        if matches!(
            inner.as_ref(),
            crate::implementation_from_dafny::_Wrappers_Compile::Result::Failure { .. }
        ) {
            // TODO: convert error - the potential types are not modeled!
            return Err(BuildError::other(
                ::aws_smithy_types::error::metadata::ErrorMetadata::builder()
                    .message("Invalid client config")
                    .build(),
            ));
        }
        Ok(Self {
            dafny_client: ::dafny_runtime::upcast_object()(inner.Extract()),
        })
    }
}

mod get_union;

mod get_union_known_value;
