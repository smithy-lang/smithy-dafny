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
            Err(crate::conversions::$snakeCaseOperationName:L::from_dafny_error(
                inner_result.error().clone(),
            ))
        }