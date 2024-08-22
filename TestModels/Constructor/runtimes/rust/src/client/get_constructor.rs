impl super::Client {
    /// Constructs a fluent builder for the [`GetConstructor`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<String>)`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder::value) / [`set_value(Option<String>)`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder::set_value):<br>required: **false**<br>(undocumented)<br>
    /// - On success, responds with [`GetConstructorOutput`](crate::operation::get_constructor::GetConstructorOutput) with field(s):
    ///   - [`internal_config_string(Option<String>)`](crate::operation::get_constructor::GetConstructorOutput::internal_config_string): (undocumented)
    ///   - [`blob_value(Option<Blob>)`](crate::operation::get_constructor::GetConstructorOutput::blob_value): (undocumented)
    ///   - [`boolean_value(Option<bool>)`](crate::operation::get_constructor::GetConstructorOutput::boolean_value): (undocumented)
    ///   - [`string_value(Option<String>)`](crate::operation::get_constructor::GetConstructorOutput::string_value): (undocumented)
    ///   - [`integer_value(Option<i32>)`](crate::operation::get_constructor::GetConstructorOutput::integer_value): (undocumented)
    ///   - [`long_value(Option<i64>)`](crate::operation::get_constructor::GetConstructorOutput::long_value): (undocumented)
    /// - On failure, responds with [`SdkError<GetConstructorError>`](crate::operation::get_constructor::GetConstructorError)
    pub fn get_constructor(
        &self,
    ) -> crate::operation::get_constructor::builders::GetConstructorFluentBuilder {
        crate::operation::get_constructor::builders::GetConstructorFluentBuilder::new(self.clone())
    }
}
