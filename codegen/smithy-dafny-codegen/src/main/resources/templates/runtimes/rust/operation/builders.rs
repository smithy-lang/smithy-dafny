pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationOutputName:L::$pascalCaseOperationOutputName:LBuilder;

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationInputName:L::$pascalCaseOperationInputName:LBuilder;

impl $pascalCaseOperationInputName:LBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        $operationTargetName:L: &$operationTargetType:L,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationErrorName:L,
    > {
        let mut fluent_builder = $operationTargetName:L.$snakeCaseOperationName:L();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `$pascalCaseOperationName:L`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct $pascalCaseOperationName:LFluentBuilder {
    $operationTargetName:L: $operationTargetType:L,
    pub(crate) inner: crate::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationInputName:LBuilder,
}
impl $pascalCaseOperationName:LFluentBuilder {
    /// Creates a new `$pascalCaseOperationName:L`.
    pub(crate) fn new($operationTargetName:L: $operationTargetType:L) -> Self {
        Self {
            $operationTargetName:L,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the $pascalCaseOperationName:L as a reference.
    pub fn as_input(&self) -> &crate::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationInputName:LBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationErrorName:L,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since $pascalCaseOperationName:L doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationErrorName:L::unhandled)?;
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationName:L::send(&self.$operationTargetName:L, input).await
    }

    $accessors:L
}