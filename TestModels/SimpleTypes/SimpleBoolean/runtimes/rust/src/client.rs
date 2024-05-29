// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use aws_smithy_types::error::operation::BuildError;

#[derive(Debug)]
pub(crate) struct Handle {
    pub(crate) conf: crate::Config,
    pub(crate) inner: ::dafny_runtime::Object<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    handle: ::std::sync::Arc<Handle>,
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(conf: crate::Config) -> Result<Self, BuildError> {
        // If this service had any configuration properties,
        // they would need converting here too.
        let inner_config = ::std::rc::Rc::new(
            ::simple_boolean_dafny::_simple_dtypes_dboolean_dinternaldafny::_default::DefaultSimpleBooleanConfig());
        let inner =
            ::simple_boolean_dafny::_simple_dtypes_dboolean_dinternaldafny::_default::SimpleBoolean(&inner_config);
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
        let handle = Handle {
            conf: conf.clone(),
            inner: ::dafny_runtime::UpcastTo::<dafny_runtime::Object<(dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient + 'static)>>::upcast_to(inner.Extract()),
        };
        Ok(Self {
            handle: ::std::sync::Arc::new(handle),
        })
    }

    /// Returns the client's configuration.
    pub fn config(&self) -> &crate::Config {
        &self.handle.conf
    }
}

mod get_boolean;