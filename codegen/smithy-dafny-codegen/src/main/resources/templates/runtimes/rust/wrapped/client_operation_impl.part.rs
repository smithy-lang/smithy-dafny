    fn $operationName:L(
        $operationInputParams:L
    ) -> dafny_runtime::Rc<
        crate::r#_Wrappers_Compile::Result<
            $operationOutputDafnyType:L,
            dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>,
        >,
    >{
        let inner_input = $inputFromDafny:L;
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on($rustRootModuleName:L::operation::$snakeCaseOperationName:L::$pascalCaseOperationName:L::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::dafny_runtime::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: $rustRootModuleName:L::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::dafny_runtime::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: $outputToDafny:L,
                },
            ),
        }
    }