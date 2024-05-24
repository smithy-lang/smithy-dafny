// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
impl super::Client {
    /// Constructs a fluent builder for the [`GetDouble`](crate::operation::get_double_known_value::builders::GetDoubleFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(Sequence<u8>)`](crate::operation::get_double_known_value::builders::GetDoubleFluentBuilder::value) / [`set_value(Option<Sequence<u8>>)`](crate::operation::get_double_known_value::builders::GetDoubleFluentBuilder::set_value):(undocumented)<br>
    /// - On success, responds with [`GetDoubleOutput`](crate::operation::get_double_known_value::GetDoubleOutput) with field(s):
    ///   - [`value(Option<Double>)`](crate::operation::get_double_known_value::GetDoubleOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetDoubleError>`](crate::operation::get_double_known_value::GetDoubleError)
    pub fn get_double_known_value(
        &self,
    ) -> crate::operation::get_double_known_value::builders::GetDoubleKnownValueFluentBuilder {
        crate::operation::get_double_known_value::builders::GetDoubleKnownValueFluentBuilder::new(
            self.handle.clone(),
        )
    }
}
