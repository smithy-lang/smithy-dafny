// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct AlwaysErrorInput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<::std::string::String>,
}
impl AlwaysErrorInput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<&str> {
        self.value.as_deref()
    }
}
impl AlwaysErrorInput {
    /// Creates a new builder-style object to manufacture [`AlwaysErrorInput`](crate::operation::operation::AlwaysErrorInput).
    pub fn builder() -> crate::operation::always_error::builders::AlwaysErrorInputBuilder {
        crate::operation::always_error::builders::AlwaysErrorInputBuilder::default()
    }
}

/// A builder for [`AlwaysErrorInput`](crate::operation::operation::AlwaysErrorInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct AlwaysErrorInputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl AlwaysErrorInputBuilder {
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
    /// Consumes the builder and constructs a [`AlwaysErrorInput`](crate::operation::operation::AlwaysErrorInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_error::AlwaysErrorInput,
        crate::types::error::Error,
    > {
        ::std::result::Result::Ok(crate::operation::always_error::AlwaysErrorInput {
            value: self.value,
        })
    }
}
