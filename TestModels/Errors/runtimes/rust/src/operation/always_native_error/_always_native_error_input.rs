// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct AlwaysNativeErrorInput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<::std::string::String>,
}
impl AlwaysNativeErrorInput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<&str> {
        self.value.as_deref()
    }
}
impl AlwaysNativeErrorInput {
    /// Creates a new builder-style object to manufacture [`AlwaysNativeErrorInput`](crate::operation::operation::AlwaysNativeErrorInput).
    pub fn builder(
    ) -> crate::operation::always_native_error::builders::AlwaysNativeErrorInputBuilder {
        crate::operation::always_native_error::builders::AlwaysNativeErrorInputBuilder::default()
    }
}

/// A builder for [`AlwaysNativeErrorInput`](crate::operation::operation::AlwaysNativeErrorInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct AlwaysNativeErrorInputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl AlwaysNativeErrorInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
        self.value = ::std::option::Option::Some(input.into());
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn set_value(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
        self.value = input;
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn get_value(&self) -> &::std::option::Option<::std::string::String> {
        &self.value
    }
    /// Consumes the builder and constructs a [`AlwaysNativeErrorInput`](crate::operation::operation::AlwaysNativeErrorInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_native_error::AlwaysNativeErrorInput,
        crate::types::error::Error,
    > {
        ::std::result::Result::Ok(
            crate::operation::always_native_error::AlwaysNativeErrorInput { value: self.value },
        )
    }
}
