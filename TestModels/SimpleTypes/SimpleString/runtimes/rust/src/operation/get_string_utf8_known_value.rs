// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetStringUTF8KnownValue`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetStringUTF8KnownValue;
impl GetStringUTF8KnownValue {
    /// Creates a new `GetStringUTF8KnownValue`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_string_utf8_known_value::GetStringUTF8Input,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8_known_value::GetStringUTF8Output,
        crate::operation::get_string_utf8_known_value::GetStringUTF8KnownValueError,
    > {
        let inner_input = crate::conversions::get_string_utf8_known_value::_get_string_utf8_known_value_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetStringUTF8KnownValue(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_string_utf8_known_value::_get_string_utf8_known_value_output::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(crate::conversions::get_string_utf8_known_value::from_dafny_error(
                inner_result.error().clone(),
            ))
        }
    }
}

/// Error type for the `GetStringUTF8KnownValue` operation.
#[non_exhaustive]
#[derive(::std::fmt::Debug)]
pub enum GetStringUTF8KnownValueError {
    /// An unexpected error occurred (e.g., invalid JSON returned by the service or an unknown error code).
    #[deprecated(
        note = "Matching `Unhandled` directly is not forwards compatible. Instead, match using a \
    variable wildcard pattern and check `.code()`:
     \
    &nbsp;&nbsp;&nbsp;`err if err.code() == Some(\"SpecificExceptionCode\") => { /* handle the error */ }`
     \
    See [`ProvideErrorMetadata`](#impl-ProvideErrorMetadata-for-GetStringUTF8KnownValueError) for what information is available for the error."
    )]
    Unhandled(crate::error::sealed_unhandled::Unhandled),
}
impl GetStringUTF8KnownValueError {
    /// Creates the `GetStringUTF8KnownValueError::Unhandled` variant from any error type.
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

    /// Creates the `GetStringUTF8KnownValueError::Unhandled` variant from an [`ErrorMetadata`](::aws_smithy_types::error::ErrorMetadata).
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
impl ::std::error::Error for GetStringUTF8KnownValueError {
    fn source(&self) -> ::std::option::Option<&(dyn ::std::error::Error + 'static)> {
        match self {
            Self::Unhandled(_inner) => ::std::option::Option::Some(&*_inner.source),
        }
    }
}
impl ::std::fmt::Display for GetStringUTF8KnownValueError {
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
impl ::aws_smithy_types::retry::ProvideErrorKind for GetStringUTF8KnownValueError {
    fn code(&self) -> ::std::option::Option<&str> {
        ::aws_smithy_types::error::metadata::ProvideErrorMetadata::code(self)
    }
    fn retryable_error_kind(&self) -> ::std::option::Option<::aws_smithy_types::retry::ErrorKind> {
        ::std::option::Option::None
    }
}
impl ::aws_smithy_types::error::metadata::ProvideErrorMetadata for GetStringUTF8KnownValueError {
    fn meta(&self) -> &::aws_smithy_types::error::ErrorMetadata {
        match self {
            Self::Unhandled(_inner) => &_inner.meta,
        }
    }
}
impl ::aws_smithy_runtime_api::client::result::CreateUnhandledError for GetStringUTF8KnownValueError {
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

pub use crate::operation::get_string_utf8_known_value::_get_string_utf8_output::GetStringUTF8Output;

pub use crate::operation::get_string_utf8_known_value::_get_string_utf8_input::GetStringUTF8Input;

pub(crate) mod _get_string_utf8_output;

pub(crate) mod _get_string_utf8_input;

/// Builders
pub mod builders;
