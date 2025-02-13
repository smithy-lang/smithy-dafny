fn r#_$operationName:L_k(
    &self,
    input: $operationDafnyInputType:L,
) -> ::dafny_runtime::Rc<
    crate::r#_Wrappers_Compile::Result<
        $operationDafnyOutputType:L,
        ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>,
    >,
>
{
    let inner_input = $inputFromDafny:L;
    let inner_result = self.obj.inner.lock().unwrap().$snakeCaseOperationName:L(inner_input);
    let result = match inner_result {
        Ok(x) => crate::r#_Wrappers_Compile::Result::Success {
            value: $outputToDafny:L,
        },
        Err(x) => crate::r#_Wrappers_Compile::Result::Failure {
            error: $rustRootModuleName:L::conversions::error::to_dafny(x),
        },
    };
    ::dafny_runtime::Rc::new(result)
}