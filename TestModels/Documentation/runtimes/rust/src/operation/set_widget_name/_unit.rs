// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// A service that supports the operation of getting things.
///
/// This is still part of the same documentation trait
/// even though it's separated.
///
/// It's also important to make sure we don't incorrectly
/// reject multiline plaintext comments
/// because we incorrectly think newlines are CommonMark
/// syntax.
pub struct Unit {

}
impl Unit {

}
impl Unit {
    /// Creates a new builder-style object to manufacture [`Unit`](crate::operation::set_widget_name::builders::Unit).
    pub fn builder() -> crate::operation::set_widget_name::builders::UnitBuilder {
        crate::operation::set_widget_name::builders::UnitBuilder::default()
    }
}

/// A builder for [`Unit`](crate::operation::operation::Unit).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct UnitBuilder {

}
impl UnitBuilder {

    /// Consumes the builder and constructs a [`Unit`](crate::operation::operation::Unit).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::set_widget_name::Unit,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::set_widget_name::Unit {

        })
    }
}
