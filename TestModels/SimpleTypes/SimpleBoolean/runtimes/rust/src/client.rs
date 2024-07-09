// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::types::simple_boolean_config::SimpleBooleanConfig,
    ) -> Result<Self, BuildError> {
        let inner =
            ::simple_boolean_dafny::_simple_dtypes_dboolean_dinternaldafny::_default::SimpleBoolean(
                &crate::conversions::simple_boolean_config::_simple_boolean_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            ::simple_boolean_dafny::_Wrappers_Compile::Result::Failure { .. }
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

mod get_boolean;
