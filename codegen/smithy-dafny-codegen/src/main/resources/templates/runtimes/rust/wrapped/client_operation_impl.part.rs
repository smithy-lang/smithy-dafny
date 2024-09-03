    fn $operationName:L(
        &mut self,
        input: &std::rc::Rc<
            crate::r#$dafnyTypesModuleName:L::$operationInputName:L,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$operationOutputName:L,
            >,
            std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::$snakeCaseOperationName:L::$operationName:L::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::$snakeCaseOperationName:L::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::to_dafny(client),
                },
            ),
        }
    }