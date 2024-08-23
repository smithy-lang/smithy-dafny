// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
/// Orchestration and serialization glue logic for `AlwaysMultipleErrors`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct AlwaysMultipleErrors;
impl AlwaysMultipleErrors {
    /// Creates a new `AlwaysMultipleErrors`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::always_multiple_errors::AlwaysMultipleErrorsInput,
    ) -> ::std::result::Result<
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsOutput,
        crate::types::error::Error,
    > {
        let inner_input =
            crate::conversions::always_multiple_errors::_always_multiple_errors_input::to_dafny(
                input,
            );
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).AlwaysMultipleErrors(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(crate::conversions::always_multiple_errors::_always_multiple_errors_output::from_dafny(inner_result.value().clone()))
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::always_multiple_errors::_always_multiple_errors_output::AlwaysMultipleErrorsOutput;

pub use crate::operation::always_multiple_errors::_always_multiple_errors_input::AlwaysMultipleErrorsInput;

mod _always_multiple_errors_input;

mod _always_multiple_errors_output;

/// Builders
pub mod builders;
