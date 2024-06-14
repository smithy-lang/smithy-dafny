// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
pub struct GetResourcesOutput {
    pub(crate) output: crate::types::simple_resource::SimpleResourceImpl,
}

impl GetResourcesOutput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn output(&self) -> crate::types::simple_resource::SimpleResourceImpl {
        self.output.clone()
    }
}

impl GetResourcesOutput {
    /// Creates a new builder-style object to manufacture [`GetResourcesOutput`](crate::operation::operation::GetResourcesOutput).
    pub fn builder() -> crate::operation::get_resources::builders::GetResourcesOutputBuilder {
        crate::operation::get_resources::builders::GetResourcesOutputBuilder::default()
    }
}

/// A builder for [`GetResourcesOutput`](crate::operation::operation::GetResourcesOutput).
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::default::Default)]
pub struct GetResourcesOutputBuilder {
    pub(crate) output: ::std::option::Option<crate::types::simple_resource::SimpleResourceImpl>,
}

impl GetResourcesOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn output(mut self, input: crate::types::simple_resource::SimpleResourceImpl) -> Self {
        self.output = ::std::option::Option::Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_output(
        mut self,
        input: ::std::option::Option<crate::types::simple_resource::SimpleResourceImpl>,
    ) -> Self {
        self.output = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_output(
        &self,
    ) -> &::std::option::Option<crate::types::simple_resource::SimpleResourceImpl> {
        &self.output
    }

    /// Consumes the builder and constructs a [`GetResourcesOutput`](crate::operation::operation::GetResourcesOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resources::GetResourcesOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resources::GetResourcesOutput {
            output: self.output.unwrap(),
        })
    }
}
