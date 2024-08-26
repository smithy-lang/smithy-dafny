// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
impl super::Client {
    /// Constructs a fluent builder for the [`AlwaysNativeError`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<String>>)`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::name) / [`set_name(Option<String>)`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::set_name):(undocumented)<br>
    /// - On success, responds with [`AlwaysNativeErrorOutput`](crate::operation::always_native_error::AlwaysNativeErrorOutput) with field(s):
    ///   - [`value(Option<String>)`](crate::operation::always_native_error::AlwaysNativeErrorOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<AlwaysNativeErrorError>`](crate::operation::always_native_error::AlwaysNativeErrorError)
    pub fn always_native_error(
        &self,
    ) -> crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder {
        crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::new(
            self.clone(),
        )
    }
}