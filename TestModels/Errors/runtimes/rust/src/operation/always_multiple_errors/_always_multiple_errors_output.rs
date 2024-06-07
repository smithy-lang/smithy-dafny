// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct AlwaysMultipleErrorsOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<::std::string::String>,
}
impl AlwaysMultipleErrorsOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<&str> {
        self.value.as_deref()
    }
}
impl AlwaysMultipleErrorsOutput {
    /// Creates a new builder-style object to manufacture [`AlwaysMultipleErrorsOutput`](crate::operation::operation::AlwaysMultipleErrorsOutput).
    pub fn builder(
    ) -> crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsOutputBuilder {
        crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsOutputBuilder::default()
    }
}

/// A builder for [`AlwaysMultipleErrorsOutput`](crate::operation::operation::AlwaysMultipleErrorsOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct AlwaysMultipleErrorsOutputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl AlwaysMultipleErrorsOutputBuilder {
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
    /// Consumes the builder and constructs a [`AlwaysMultipleErrorsOutput`](crate::operation::operation::AlwaysMultipleErrorsOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(
            crate::operation::always_multiple_errors::AlwaysMultipleErrorsOutput {
                value: self.value,
            },
        )
    }
}
