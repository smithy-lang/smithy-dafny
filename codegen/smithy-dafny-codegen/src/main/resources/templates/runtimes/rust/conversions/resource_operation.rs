
impl crate::$dafnyTypesModuleName:L::$dafnyResourceName:L
  for $rustResourceName:LWrapper
{
  fn r#_GetResourceData_k(
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
}

impl crate::types::$snakeCaseResourceName:L::$rustResourceName:L for $dafnyResourceName:LDafnyWrapper {
  fn get_resource_data(
      &mut self,
      input: crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationInputName:L,
  ) -> Result<
      crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
      $qualifiedRustServiceErrorType:L,
  > {
      let inner_input =
          crate::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::to_dafny(input);
      let inner_result = ::dafny_runtime::md!(self.obj.clone()).$operationName:L(&inner_input);
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
