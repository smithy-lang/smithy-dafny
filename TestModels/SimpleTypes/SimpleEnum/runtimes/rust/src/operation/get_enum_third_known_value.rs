// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
/// Orchestration and serialization glue logic for `GetEnumThirdKnownValue`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetEnumThirdKnownValue;
impl GetEnumThirdKnownValue {
    /// Creates a new `GetEnumThirdKnownValue`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_enum_third_known_value::GetEnumThirdKnownValueInput,
    ) -> ::std::result::Result<
        crate::operation::get_enum_third_known_value::GetEnumThirdKnownValueOutput,
        crate::operation::get_enum_third_known_value::GetEnumThirdKnownValueError,
    > {
        let inner_input =
            crate::conversions::get_enum_third_known_value::_get_enum_third_known_value_input::to_dafny(input);
        let inner_result = ::dafny_runtime::md!(client.dafny_client.clone()).GetEnum(&inner_input);
        if matches!(
            inner_result.as_ref(),
            ::simple_enum_dafny::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_enum_third_known_value::_get_enum_third_known_value_output::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(
                crate::conversions::get_enum_third_known_value::from_dafny_error(
                    inner_result.error().clone(),
                ),
            )
        }
    }
}

/// Error type for the `GetEnumThirdKnownValue` operation.
#[non_exhaustive]
#[derive(::std::fmt::Debug)]
pub enum GetEnumThirdKnownValueError {
    /// An unexpected error occurred (e.g., invalid JSON returned by the service or an unthird_known error code).
    #[deprecated(
        note = "Matching `Unhandled` directly is not forwards compatible. Instead, match using a \
    variable wildcard pattern and check `.code()`:
     \
    &nbsp;&nbsp;&nbsp;`err if err.code() == Some(\"SpecificExceptionCode\") => { /* handle the error */ }`
     \
    See [`ProvideErrorMetadata`](#impl-ProvideErrorMetadata-for-GetEnumThirdKnownValueError) for what information is available for the error."
    )]
    Unhandled(crate::error::sealed_unhandled::Unhandled),
}
impl GetEnumThirdKnownValueError {
    /// Creates the `GetEnumThirdKnownValueError::Unhandled` variant from any error type.
    pub fn unhandled(
        err: impl ::std::convert::Into<
            ::std::boxed::Box<
                dyn ::std::error::Error + ::std::marker::Send + ::std::marker::Sync + 'static,
            >,
        >,
    ) -> Self {
        Self::Unhandled(crate::error::sealed_unhandled::Unhandled {
            source: err.into(),
            meta: ::std::default::Default::default(),
        })
    }

    /// Creates the `GetEnumThirdKnownValueError::Unhandled` variant from an [`ErrorMetadata`](::aws_smithy_types::error::ErrorMetadata).
    pub fn generic(err: ::aws_smithy_types::error::ErrorMetadata) -> Self {
        Self::Unhandled(crate::error::sealed_unhandled::Unhandled {
            source: err.clone().into(),
            meta: err,
        })
    }
    ///
    /// Returns error metadata, which includes the error code, message,
    /// request ID, and potentially additional information.
    ///
    pub fn meta(&self) -> &::aws_smithy_types::error::ErrorMetadata {
        match self {
            Self::Unhandled(e) => &e.meta,
        }
    }
}
impl ::std::error::Error for GetEnumThirdKnownValueError {
    fn source(&self) -> ::std::option::Option<&(dyn ::std::error::Error + 'static)> {
        match self {
            Self::Unhandled(_inner) => ::std::option::Option::Some(&*_inner.source),
        }
    }
}
impl ::std::fmt::Display for GetEnumThirdKnownValueError {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        match self {
            Self::Unhandled(_inner) => {
                if let ::std::option::Option::Some(code) =
                    ::aws_smithy_types::error::metadata::ProvideErrorMetadata::code(self)
                {
                    write!(f, "unhandled error ({code})")
                } else {
                    f.write_str("unhandled error")
                }
            }
        }
    }
}
impl ::aws_smithy_types::retry::ProvideErrorKind for GetEnumThirdKnownValueError {
    fn code(&self) -> ::std::option::Option<&str> {
        ::aws_smithy_types::error::metadata::ProvideErrorMetadata::code(self)
    }
    fn retryable_error_kind(&self) -> ::std::option::Option<::aws_smithy_types::retry::ErrorKind> {
        ::std::option::Option::None
    }
}
impl ::aws_smithy_types::error::metadata::ProvideErrorMetadata for GetEnumThirdKnownValueError {
    fn meta(&self) -> &::aws_smithy_types::error::ErrorMetadata {
        match self {
            Self::Unhandled(_inner) => &_inner.meta,
        }
    }
}
impl ::aws_smithy_runtime_api::client::result::CreateUnhandledError
    for GetEnumThirdKnownValueError
{
    fn create_unhandled_error(
        source: ::std::boxed::Box<
            dyn ::std::error::Error + ::std::marker::Send + ::std::marker::Sync + 'static,
        >,
        meta: ::std::option::Option<::aws_smithy_types::error::ErrorMetadata>,
    ) -> Self {
        Self::Unhandled(crate::error::sealed_unhandled::Unhandled {
            source,
            meta: meta.unwrap_or_default(),
        })
    }
}

pub use crate::operation::get_enum_third_known_value::_get_enum_third_known_value_output::GetEnumThirdKnownValueOutput;

pub use crate::operation::get_enum_third_known_value::_get_enum_third_known_value_input::GetEnumThirdKnownValueInput;

mod _get_enum_third_known_value_input;

mod _get_enum_third_known_value_output;

/// Builders
pub mod builders;
