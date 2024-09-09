/// Orchestration and serialization glue logic for `$pascalCaseOperationName:L`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct $pascalCaseOperationName:L;
impl $pascalCaseOperationName:L {
    /// Creates a new `$pascalCaseOperationName:L`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationInputName:L,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        crate::types::error::Error,
    > {
        let inner_input = crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).$operationName:L(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationOutputName:L::$pascalCaseOperationOutputName:L;

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationInputName:L::$pascalCaseOperationInputName:L;

pub(crate) mod _$snakeCaseOperationOutputName:L;

pub(crate) mod _$snakeCaseOperationInputName:L;

/// Builders
pub mod builders;