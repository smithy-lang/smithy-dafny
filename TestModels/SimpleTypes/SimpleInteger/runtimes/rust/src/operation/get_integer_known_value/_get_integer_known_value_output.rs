// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetIntegerKnownValueOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub value: ::std::option::Option<i32>,
}
impl GetIntegerKnownValueOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(&self) -> ::std::option::Option<i32> {
        self.value
    }
}
impl GetIntegerKnownValueOutput {
    /// Creates a new builder-style object to manufacture [`GetIntegerKnownValueOutput`](crate::operation::operation::GetIntegerKnownValueOutput).
    pub fn builder(
    ) -> crate::operation::get_integer_known_value::builders::GetIntegerKnownValueOutputBuilder {
        crate::operation::get_integer_known_value::builders::GetIntegerKnownValueOutputBuilder::default()
    }
}

/// A builder for [`GetIntegerKnownValueOutput`](crate::operation::operation::GetIntegerKnownValueOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetIntegerKnownValueOutputBuilder {
    pub(crate) value: ::std::option::Option<i32>,
}
impl GetIntegerKnownValueOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn value(
        mut self,
        input: impl ::std::convert::Into<i32>,
    ) -> Self {
        self.value = ::std::option::Option::Some(input.into());
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn set_value(
        mut self,
        input: ::std::option::Option<i32>,
    ) -> Self {
        self.value = input;
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn get_value(&self) -> &::std::option::Option<i32> {
        &self.value
    }
    /// Consumes the builder and constructs a [`GetIntegerKnownValueOutput`](crate::operation::operation::GetIntegerKnownValueOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_integer_known_value::GetIntegerKnownValueOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(
            crate::operation::get_integer_known_value::GetIntegerKnownValueOutput { value: self.value },
        )
    }
}
