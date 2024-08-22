// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct AlwaysMultipleErrorsInput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<::std::string::String>,
}
impl AlwaysMultipleErrorsInput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<&str> {
        self.value.as_deref()
    }
}
impl AlwaysMultipleErrorsInput {
    /// Creates a new builder-style object to manufacture [`AlwaysMultipleErrorsInput`](crate::operation::operation::AlwaysMultipleErrorsInput).
    pub fn builder(
    ) -> crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsInputBuilder {
        crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsInputBuilder::default(
        )
    }
}

/// A builder for [`AlwaysMultipleErrorsInput`](crate::operation::operation::AlwaysMultipleErrorsInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct AlwaysMultipleErrorsInputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl AlwaysMultipleErrorsInputBuilder {
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
    /// Consumes the builder and constructs a [`AlwaysMultipleErrorsInput`](crate::operation::operation::AlwaysMultipleErrorsInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsInput,
        crate::types::error::Error,
    > {
        ::std::result::Result::Ok(
            crate::operation::always_multiple_errors::AlwaysMultipleErrorsInput {
                value: self.value,
            },
        )
    }
}