// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use aws_smithy_types::error::operation::BuildError;

#[derive(Debug)]
pub(crate) struct Handle {
    pub(crate) conf: crate::Config,
    pub(crate) inner: *mut dyn crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient
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
            crate::implementation_from_dafny::_simple_dtypes_dsmithystring_dinternaldafny::_default::DefaultSimpleStringConfig());
        let inner =
            crate::implementation_from_dafny::_simple_dtypes_dsmithystring_dinternaldafny::_default::SimpleString(&inner_config);
        if matches!(inner.as_ref(), crate::implementation_from_dafny::_Wrappers_Compile::Result::Failure { .. }) {
            // TODO: convert error - the potential types are not modeled!
            return Err(BuildError::other(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Invalid client config").build()));
        }
        let handle = Handle {
            conf: conf.clone(),
            inner: inner.Extract()
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

impl Drop for Handle {
    fn drop(&mut self) {
        // Ensure the Dafny values we created by calling SimpleString are deallocated.
        unsafe { drop(Box::from_raw(self.inner)); }
    }
}

mod get_string;

mod get_string_single_value;

mod get_string_utf8;

