fn r#_$operationName:L_k(
    &mut self,
    input: &::std::rc::Rc<
    crate::r#$dafnyTypesModuleName:L::$pascalCaseOperationInputName:L,
    >,
) -> ::std::rc::Rc<
    crate::r#_Wrappers_Compile::Result<
        ::std::rc::Rc<
        crate::r#$dafnyTypesModuleName:L::$pascalCaseOperationOutputName:L,
        >,
        ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>,
    >,
>
{
    let inner_input =
        crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::from_dafny(
            input.clone(),
        );
    let inner_result = self.obj.inner.borrow_mut().$snakeCaseOperationName:L(inner_input);
    let result = match inner_result {
        Ok(x) => crate::r#_Wrappers_Compile::Result::Success {
            value: crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::to_dafny(
                x,
            ),
        },
        Err(x) => crate::r#_Wrappers_Compile::Result::Failure {
            error: crate::conversions::error::to_dafny(x),
        },
    };
    ::std::rc::Rc::new(result)
}