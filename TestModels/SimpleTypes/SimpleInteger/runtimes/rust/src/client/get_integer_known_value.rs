// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
impl super::Client {
    /// Constructs a fluent builder for the [`GetInteger`](crate::operation::get_integer_known_value::builders::GetIntegerFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(i32)`](crate::operation::get_integer_known_value::builders::GetIntegerFluentBuilder::value) / [`set_value(Option<i32>)`](crate::operation::get_integer_known_value::builders::GetIntegerFluentBuilder::set_value):(undocumented)<br>
    /// - On success, responds with [`GetIntegerOutput`](crate::operation::get_integer_known_value::GetIntegerOutput) with field(s):
    ///   - [`value(Option<Integer>)`](crate::operation::get_integer_known_value::GetIntegerOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetIntegerError>`](crate::operation::get_integer_known_value::GetIntegerError)
    pub fn get_integer_known_value(
        &self,
    ) -> crate::operation::get_integer_known_value::builders::GetIntegerKnownValueFluentBuilder
    {
        crate::operation::get_integer_known_value::builders::GetIntegerKnownValueFluentBuilder::new(
            self.clone(),
        )
    }
}
