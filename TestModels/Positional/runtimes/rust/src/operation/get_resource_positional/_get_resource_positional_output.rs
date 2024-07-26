// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetResourcePositionalOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub output: crate::SimpleResourceReference,
}
impl GetResourcePositionalOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn output(&self) -> &crate::SimpleResourceReference {
        &self.output
    }
}
impl GetResourcePositionalOutput {
    /// Creates a new builder-style object to manufacture [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::GetResourcePositionalOutput).
    pub fn builder(
    ) -> crate::operation::get_resource_positional::builders::GetResourcePositionalOutputBuilder
    {
        crate::operation::get_resource_positional::builders::GetResourcePositionalOutputBuilder::default()
    }
}

/// A builder for [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::GetResourcePositionalOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetResourcePositionalOutputBuilder {
    pub(crate) output: ::std::option::Option<crate::SimpleResourceReference>,
}
impl GetResourcePositionalOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    /// This field is required.
    pub fn output(mut self, input: crate::SimpleResourceReference) -> Self {
        self.output = ::std::option::Option::Some(input);
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn set_output(
        mut self,
        input: ::std::option::Option<crate::SimpleResourceReference>,
    ) -> Self {
        self.output = input;
        self
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn get_output(&self) -> &::std::option::Option<crate::SimpleResourceReference> {
        &self.output
    }
    /// Consumes the builder and constructs a [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::GetResourcePositionalOutput).
    /// This method will fail if any of the following fields are not set:
    /// - [`output`](crate::operation::get_resource_positional::builders::GetResourcePositionalOutputBuilder::output)
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resource_positional::GetResourcePositionalOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resource_positional::GetResourcePositionalOutput {
            output: self.output.ok_or_else(|| {
                ::aws_smithy_types::error::operation::BuildError::missing_field(
                    "output",
                    "output was not specified but it is required when building GetResourcePositionalOutput",
                )
            })?,
        })
    }
}
