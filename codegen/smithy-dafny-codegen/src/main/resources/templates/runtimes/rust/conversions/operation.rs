use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: crate::operation::$snakeCaseOperationName:L::$operationErrorName:L,
) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    match value {
    crate::operation::$snakeCaseOperationName:L::$operationErrorName:L::Unhandled(unhandled) =>
      ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(unhandled)) })
  }
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
        crate::r#$dafnyTypesModuleName:L::Error,
    >,
) -> crate::operation::$snakeCaseOperationName:L::$operationErrorName:L {
    // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
    if matches!(&dafny_value.as_ref(), crate::r#$dafnyTypesModuleName:L::Error::CollectionOfErrors { .. }) {
    let error_message = "TODO: can't get message yet";
    crate::operation::$snakeCaseOperationName:L::$operationErrorName:L::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message(error_message).build())
  } else {
    crate::operation::$snakeCaseOperationName:L::$operationErrorName:L::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
  }
}

pub mod _$snakeCaseSyntheticOperationInputName:L;

pub mod _$snakeCaseSyntheticOperationOutputName:L;