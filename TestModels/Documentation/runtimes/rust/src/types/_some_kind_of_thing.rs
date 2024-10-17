// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// Either kind of thing.
pub enum SomeKindOfThing {
    #[allow(missing_docs)]
Thing(crate::types::Thing),
#[allow(missing_docs)]
Widget(crate::types::widget::WidgetRef),
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
impl SomeKindOfThing {
    /// Tries to convert the enum instance into [`Thing`](crate::types::SomeKindOfThing::Thing), extracting the inner [`crate::types::Thing`](crate::types::Thing).
/// Returns `Err(&Self)` if it can't be converted.
pub fn as_thing(&self) -> ::std::result::Result<&crate::types::Thing, &Self> {
    if let crate::types::SomeKindOfThing::Thing(val) = &self {
        ::std::result::Result::Ok(val)
    } else {
        ::std::result::Result::Err(self)
    }
}
/// Tries to convert the enum instance into [`Widget`](crate::types::SomeKindOfThing::Widget), extracting the inner [`crate::types::widget::WidgetRef`](crate::types::widget::WidgetRef).
/// Returns `Err(&Self)` if it can't be converted.
pub fn as_widget(&self) -> ::std::result::Result<&crate::types::widget::WidgetRef, &Self> {
    if let crate::types::SomeKindOfThing::Widget(val) = &self {
        ::std::result::Result::Ok(val)
    } else {
        ::std::result::Result::Err(self)
    }
}
    /// Returns true if this is a [`Thing`](crate::types::SomeKindOfThing::Thing).
pub fn is_thing(&self) -> ::std::primitive::bool {
    self.as_thing().is_ok()
}
/// Returns true if this is a [`Widget`](crate::types::SomeKindOfThing::Widget).
pub fn is_widget(&self) -> ::std::primitive::bool {
    self.as_widget().is_ok()
}
    /// Returns true if the enum instance is the `Unknown` variant.
    pub fn is_unknown(&self) -> ::std::primitive::bool {
        matches!(self, Self::Unknown)
    }
}
