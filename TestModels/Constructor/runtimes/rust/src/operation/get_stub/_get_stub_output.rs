// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetStubOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<crate::Stub>,
}

impl GetStubOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<crate::Stub> {
        self.value
    }
}

impl GetStubOutput {
    /// Creates a new builder-style object to manufacture [`GetStubOutput`](crate::operation::operation::GetStubOutput).
    pub fn builder() -> crate::operation::get_stub::builders::GetStubOutputBuilder {
        crate::operation::get_stub::builders::GetStubOutputBuilder::default()
    }
}

/// A builder for [`GetStubOutput`](crate::operation::operation::GetStubOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetStubOutputBuilder {
    pub(crate) value: ::std::option::Option<crate::Stub>,
}

impl GetStubOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(mut self, input: impl ::std::convert::Into<stub_dafny::Stub>) -> Self {
        self.value = ::std::option::Option::Some(input.into());
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_value(mut self, input: ::std::option::Option<stub_dafny::Stub>) -> Self {
        self.value = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_value(&self) -> &::std::option::Option<stub_dafny::Stub> {
        &self.value
    }

    /// Consumes the builder and constructs a [`GetStubOutput`](crate::operation::operation::GetStubOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_stub::GetStubOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_stub::GetStubOutput { value: self.value })
    }
}
