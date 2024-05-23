// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>,
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(conf: crate::Config) -> Result<Self, BuildError> {
        // let inner =
        //     ::simple_integer_dafny::_simple_dtypes_dinteger_dinternaldafny::_default::SimpleInteger(
        //         &crate::conversions::simple_integer_config::_simple_integer_config::to_dafny(conf),
        //     );

        let inner =
            ::constructor_dafny::r#_simple_dconstructor_dinternaldafny::_default::SimpleConstructor(
                &crate::conversions::simple_constructor_config::_simple_constructor_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            ::constructor_dafny::_Wrappers_Compile::Result::Failure { .. }
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

mod get_constructor;
