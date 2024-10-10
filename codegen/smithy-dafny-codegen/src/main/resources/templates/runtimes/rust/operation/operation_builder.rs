impl $operationTargetType:L {
    /// Constructs a fluent builder for the [`$operationName:L`](crate::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationName:LFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
$builderSettersDoc:L
    /// - On success, responds with [`$pascalCaseOperationOutputName:L`](crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L) with field(s):
$outputDoc:L
    /// - On failure, responds with [`SdkError<$pascalCaseOperationErrorName:L>`](crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationErrorName:L)
    pub fn $snakeCaseOperationName:L(&self) -> $rustRootModuleName:L::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationName:LFluentBuilder {
        $rustRootModuleName:L::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationName:LFluentBuilder::new(self.clone())
    }
}