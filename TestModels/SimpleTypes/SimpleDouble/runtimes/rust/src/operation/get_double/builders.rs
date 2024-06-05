// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
pub use crate::operation::get_double::_get_double_output::GetDoubleOutputBuilder;

pub use crate::operation::get_double::_get_double_input::GetDoubleInputBuilder;

impl GetDoubleInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_double::GetDoubleOutput,
        crate::operation::get_double::GetDoubleError,
    > {
        let mut fluent_builder = client.get_double();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetDouble`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetDoubleFluentBuilder {
    handle: ::std::sync::Arc<crate::client::Handle>,
    inner: crate::operation::get_double::builders::GetDoubleInputBuilder,
    config_override: ::std::option::Option<crate::config::Builder>,
}
impl GetDoubleFluentBuilder {
    /// Creates a new `GetDouble`.
    pub(crate) fn new(handle: ::std::sync::Arc<crate::client::Handle>) -> Self {
        Self {
            handle,
            inner: ::std::default::Default::default(),
            config_override: ::std::option::Option::None,
        }
    }
    /// Access the GetDouble as a reference.
    pub fn as_input(&self) -> &crate::operation::get_double::builders::GetDoubleInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_double::GetDoubleOutput,
        crate::operation::get_double::GetDoubleError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetDouble doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_double::GetDoubleError::unhandled)?;
        crate::operation::get_double::GetDouble::send(&self.handle, input).await
    }

    pub(crate) fn config_override(
        mut self,
        config_override: impl Into<crate::config::Builder>,
    ) -> Self {
        self.set_config_override(Some(config_override.into()));
        self
    }

    pub(crate) fn set_config_override(
        &mut self,
        config_override: Option<crate::config::Builder>,
    ) -> &mut Self {
        self.config_override = config_override;
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(mut self, input: f64) -> Self {
        self.inner = self.inner.value(input);
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn set_value(mut self, input: ::std::option::Option<f64>) -> Self {
        self.inner = self.inner.set_value(input);
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn get_value(&self) -> &::std::option::Option<f64> {
        self.inner.get_value()
    }
}
