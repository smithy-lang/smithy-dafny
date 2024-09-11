// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
impl super::Client {
    /// Constructs a fluent builder for the [`GetResourcePositional`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`name(impl Into<String>)`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::name) / [`set_name(Option<String>)`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::set_name):<br>required: **true**<br>(undocumented)<br>
    /// - On success, responds with [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::GetResourcePositionalOutput) with field(s):
    ///   - [`output(SimpleResourceReference)`](crate::operation::get_resource_positional::GetResourcePositionalOutput::output): (undocumented)
    /// - On failure, responds with [`SdkError<GetResourcePositionalError>`](crate::operation::get_resource_positional::GetResourcePositionalError)
    pub fn get_resource_positional(
        &self
    ) -> crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder
    {
        crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::new(
            self.clone(),
        )
    }
}
