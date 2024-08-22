// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

/// Configuration for a simple service client.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SimpleConstructorConfig {
    pub(crate) blob_value: Option<Vec<u8>>,
    pub(crate) boolean_value: Option<bool>,
    pub(crate) string_value: Option<String>,
    pub(crate) integer_value: Option<i32>,
    pub(crate) long_value: Option<i64>,
}

impl SimpleConstructorConfig {
    /// Constructs a config builder.
    pub fn builder() -> Builder {
        Builder::default()
    }
    /// Converts this config back into a builder so that it can be tweaked.
    pub fn to_builder(&self) -> Builder {
        Builder {
            blob_value: self.blob_value.clone(),
            boolean_value: self.boolean_value,
            string_value: self.string_value.clone(),
            integer_value: self.integer_value,
            long_value: self.long_value,
        }
    }
}
/// Builder for creating a `Config`.
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Builder {
    pub(crate) blob_value: Option<Vec<u8>>,
    pub(crate) boolean_value: Option<bool>,
    pub(crate) string_value: Option<String>,
    pub(crate) integer_value: Option<i32>,
    pub(crate) long_value: Option<i64>,
}
impl ::std::default::Default for Builder {
    fn default() -> Self {
        Self {
            blob_value: Some(vec![0]),
            boolean_value: Some(false),
            string_value: Some("".to_string()),
            integer_value: Some(0),
            long_value: Some(0),
        }
    }
}
impl Builder {
    /// Constructs a config builder.
    pub fn new() -> Self {
        Self::default()
    }

    pub fn blob_value(mut self, blob_value: Vec<u8>) -> Self {
        self.set_blob_value(Some(blob_value));
        self
    }

    pub fn set_blob_value(&mut self, blob_value: Option<Vec<u8>>) -> &mut Self {
        self.blob_value = blob_value;
        self
    }

    pub fn boolean_value(mut self, boolean_value: bool) -> Self {
        self.set_boolean_value(Some(boolean_value));
        self
    }

    pub fn set_boolean_value(&mut self, boolean_value: Option<bool>) -> &mut Self {
        self.boolean_value = boolean_value;
        self
    }

    pub fn string_value(mut self, string_value: String) -> Self {
        self.set_string_value(Some(string_value));
        self
    }

    pub fn set_string_value(&mut self, string_value: Option<String>) -> &mut Self {
        self.string_value = string_value;
        self
    }

    pub fn integer_value(mut self, integer_value: i32) -> Self {
        self.set_integer_value(Some(integer_value));
        self
    }

    pub fn set_integer_value(&mut self, integer_value: Option<i32>) -> &mut Self {
        self.integer_value = integer_value;
        self
    }

    pub fn long_value(mut self, long_value: i64) -> Self {
        self.set_long_value(Some(long_value));
        self
    }

    pub fn set_long_value(&mut self, long_value: Option<i64>) -> &mut Self {
        self.long_value = long_value;
        self
    }

    /// Builds a [`Config`].
    #[allow(unused_mut)]
    pub fn build(mut self) -> SimpleConstructorConfig {
        SimpleConstructorConfig {
            blob_value: self.blob_value,
            boolean_value: self.boolean_value,
            string_value: self.string_value,
            integer_value: self.integer_value,
            long_value: self.long_value,
        }
    }
}

pub use ::aws_smithy_runtime_api::client::behavior_version::BehaviorVersion;
