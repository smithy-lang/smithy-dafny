// Code intended to be generated software.amazon.smithy.rust.codegen.smithy-rs.
#[derive(Debug)]
pub(crate) struct Handle {
    pub(crate) conf: crate::Config,
    pub(crate) inner: crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    handle: ::std::sync::Arc<Handle>,
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(conf: crate::Config) -> Self {
        let handle = Handle {
            conf: conf.clone()
        };
        Self {
            handle: ::std::sync::Arc::new(handle),
        }
    }

    /// Returns the client's configuration.
    pub fn config(&self) -> &crate::Config {
        &self.handle.conf
    }
}

mod get_string;

mod get_string_single_value;

mod get_string_utf8;
