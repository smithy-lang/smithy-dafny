// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub enum KnownValueUnion {
    #[allow(missing_docs)] // documentation missing in model
Value(::std::primitive::i32),
    /// The `Unknown` variant represents cases where new union variant was received. Consider upgrading the SDK to the latest available version.
    /// An unknown enum variant
    ///
    /// _Note: If you encounter this error, consider upgrading your SDK to the latest version._
    /// The `Unknown` variant represents cases where the server sent a value that wasn't recognized
    /// by the client. This can happen when the server adds new functionality, but the client has not been updated.
    /// To investigate this, consider turning on debug logging to print the raw HTTP response.
    #[non_exhaustive]
    Unknown,
}
impl KnownValueUnion {
    /// Tries to convert the enum instance into [`Value`](crate::types::KnownValueUnion::Value), extracting the inner [`::std::primitive::i32`](::std::primitive::i32).
/// Returns `Err(&Self)` if it can't be converted.
pub fn as_value(&self) -> ::std::result::Result<&::std::primitive::i32, &Self> {
    if let crate::types::KnownValueUnion::Value(val) = &self {
        ::std::result::Result::Ok(val)
    } else {
        ::std::result::Result::Err(self)
    }
}
    /// Returns true if this is a [`Value`](crate::types::KnownValueUnion::Value).
pub fn is_value(&self) -> ::std::primitive::bool {
    self.as_value().is_ok()
}
    /// Returns true if the enum instance is the `Unknown` variant.
    pub fn is_unknown(&self) -> ::std::primitive::bool {
        matches!(self, Self::Unknown)
    }
}
