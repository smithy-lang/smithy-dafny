fn $snakeCaseOperationName:L(
  &self,
  input: $operationInputType:L,
) -> Result<
  $operationOutputType:L,
  $qualifiedRustServiceErrorType:L,
> {
  let inner_input = $inputToDafny:L;
  let inner_result = ::dafny_runtime::md!(self.obj.clone()).$operationName:L(&inner_input);
  if matches!(
      inner_result.as_ref(),
      crate::r#_Wrappers_Compile::Result::Success { .. }
  ) {
      Ok(
          $outputFromDafny:L,
      )
  } else {
      Err($rustRootModuleName:L::conversions::error::from_dafny(
          inner_result.error().clone(),
      ))
  }
}