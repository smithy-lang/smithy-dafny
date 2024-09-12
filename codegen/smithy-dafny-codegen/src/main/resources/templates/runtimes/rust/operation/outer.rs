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
        $operationTargetName:L: &$operationTargetType:L,
        input: crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationInputName:L,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        $qualifiedRustServiceErrorType:L,
    > {
        $inputValidations:L
        $operationSendBody:L
    }
}

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationOutputName:L::$pascalCaseOperationOutputName:L;

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationInputName:L::$pascalCaseOperationInputName:L;

pub(crate) mod _$snakeCaseOperationOutputName:L;

pub(crate) mod _$snakeCaseOperationInputName:L;

/// Builders
pub mod builders;