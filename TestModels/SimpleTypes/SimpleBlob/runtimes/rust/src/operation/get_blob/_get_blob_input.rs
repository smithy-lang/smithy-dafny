// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBlobInput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
}
impl GetBlobInput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn message(
        &self,
    ) -> ::std::option::Option<&::dafny_runtime::Sequence<::std::primitive::u8>> {
        self.value.as_ref()
    }
}
impl GetBlobInput {
    /// Creates a new builder-style object to manufacture [`GetBlobInput`](crate::operation::operation::GetBlobInput).
    pub fn builder() -> crate::operation::get_blob::builders::GetBlobInputBuilder {
        crate::operation::get_blob::builders::GetBlobInputBuilder::default()
    }
}

/// A builder for [`GetBlobInput`](crate::operation::operation::GetBlobInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBlobInputBuilder {
    pub(crate) value: ::std::option::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
}
impl GetBlobInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(
        mut self,
        input: impl ::std::convert::Into<::dafny_runtime::Sequence<::std::primitive::u8>>,
    ) -> Self {
        self.value = ::std::option::Option::Some(input.into());
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn set_value(
        mut self,
        input: ::std::option::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
    ) -> Self {
        self.value = input;
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn get_value(
        &self,
    ) -> ::std::option::Option<&::dafny_runtime::Sequence<::std::primitive::u8>> {
        self.value.as_ref()
    }
    /// Consumes the builder and constructs a [`GetBlobInput`](crate::operation::operation::GetBlobInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_blob::GetBlobInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_blob::GetBlobInput { value: self.value })
    }
}
