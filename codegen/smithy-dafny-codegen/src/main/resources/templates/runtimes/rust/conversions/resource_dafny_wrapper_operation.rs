fn $snakeCaseOperationName:L(
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