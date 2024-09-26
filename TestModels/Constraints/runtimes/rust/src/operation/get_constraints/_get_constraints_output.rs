// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetConstraintsOutput {
    #[allow(missing_docs)] // documentation missing in model
pub blob_less_than_or_equal_to_ten: ::std::option::Option<::aws_smithy_types::Blob>,
#[allow(missing_docs)] // documentation missing in model
pub greater_than_one: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub less_than_ten: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub list_less_than_or_equal_to_ten: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub map_less_than_or_equal_to_ten: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub my_blob: ::std::option::Option<::aws_smithy_types::Blob>,
#[allow(missing_docs)] // documentation missing in model
pub my_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub my_list_of_utf8_bytes: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub my_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub my_string: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub my_utf8_bytes: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub non_empty_blob: ::std::option::Option<::aws_smithy_types::Blob>,
#[allow(missing_docs)] // documentation missing in model
pub non_empty_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub non_empty_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub non_empty_string: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub one_to_ten: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub string_less_than_or_equal_to_ten: ::std::option::Option<::std::string::String>,
#[allow(missing_docs)] // documentation missing in model
pub that_ten_to_ten: ::std::option::Option<::std::primitive::i64>,
}
impl GetConstraintsOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn blob_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.blob_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn greater_than_one(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.greater_than_one
}
#[allow(missing_docs)] // documentation missing in model
pub fn less_than_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.less_than_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn list_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.list_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn map_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.map_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.my_blob
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.my_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list_of_utf8_bytes(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.my_list_of_utf8_bytes
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.my_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_string(&self) -> &::std::option::Option<::std::string::String> {
    &self.my_string
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_utf8_bytes(&self) -> &::std::option::Option<::std::string::String> {
    &self.my_utf8_bytes
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.non_empty_blob
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.non_empty_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.non_empty_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_string(&self) -> &::std::option::Option<::std::string::String> {
    &self.non_empty_string
}
#[allow(missing_docs)] // documentation missing in model
pub fn one_to_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.one_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::string::String> {
    &self.string_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn that_ten_to_ten(&self) -> &::std::option::Option<::std::primitive::i64> {
    &self.that_ten_to_ten
}
}
impl GetConstraintsOutput {
    /// Creates a new builder-style object to manufacture [`GetConstraintsOutput`](crate::operation::get_constraints::builders::GetConstraintsOutput).
    pub fn builder() -> crate::operation::get_constraints::builders::GetConstraintsOutputBuilder {
        crate::operation::get_constraints::builders::GetConstraintsOutputBuilder::default()
    }
}

/// A builder for [`GetConstraintsOutput`](crate::operation::operation::GetConstraintsOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetConstraintsOutputBuilder {
    pub(crate) blob_less_than_or_equal_to_ten: ::std::option::Option<::aws_smithy_types::Blob>,
pub(crate) greater_than_one: ::std::option::Option<::std::primitive::i32>,
pub(crate) less_than_ten: ::std::option::Option<::std::primitive::i32>,
pub(crate) list_less_than_or_equal_to_ten: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) map_less_than_or_equal_to_ten: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
pub(crate) my_blob: ::std::option::Option<::aws_smithy_types::Blob>,
pub(crate) my_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) my_list_of_utf8_bytes: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) my_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
pub(crate) my_string: ::std::option::Option<::std::string::String>,
pub(crate) my_utf8_bytes: ::std::option::Option<::std::string::String>,
pub(crate) non_empty_blob: ::std::option::Option<::aws_smithy_types::Blob>,
pub(crate) non_empty_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) non_empty_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
pub(crate) non_empty_string: ::std::option::Option<::std::string::String>,
pub(crate) one_to_ten: ::std::option::Option<::std::primitive::i32>,
pub(crate) string_less_than_or_equal_to_ten: ::std::option::Option<::std::string::String>,
pub(crate) that_ten_to_ten: ::std::option::Option<::std::primitive::i64>,
}
impl GetConstraintsOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn blob_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.blob_less_than_or_equal_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_blob_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.blob_less_than_or_equal_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_blob_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.blob_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn greater_than_one(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.greater_than_one = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_greater_than_one(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.greater_than_one = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_greater_than_one(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.greater_than_one
}
#[allow(missing_docs)] // documentation missing in model
pub fn less_than_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.less_than_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_less_than_ten(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.less_than_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_less_than_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.less_than_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn list_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.list_less_than_or_equal_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_list_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.list_less_than_or_equal_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_list_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.list_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn map_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.map_less_than_or_equal_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_map_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.map_less_than_or_equal_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_map_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.map_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_blob(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.my_blob = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_blob(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.my_blob = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.my_blob
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.my_list = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.my_list = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.my_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list_of_utf8_bytes(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.my_list_of_utf8_bytes = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_list_of_utf8_bytes(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.my_list_of_utf8_bytes = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_list_of_utf8_bytes(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.my_list_of_utf8_bytes
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.my_map = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.my_map = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.my_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_string(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.my_string = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_string(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.my_string = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_string(&self) -> &::std::option::Option<::std::string::String> {
    &self.my_string
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_utf8_bytes(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.my_utf8_bytes = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_utf8_bytes(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.my_utf8_bytes = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_utf8_bytes(&self) -> &::std::option::Option<::std::string::String> {
    &self.my_utf8_bytes
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_blob(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.non_empty_blob = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_blob(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.non_empty_blob = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.non_empty_blob
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.non_empty_list = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.non_empty_list = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.non_empty_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.non_empty_map = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.non_empty_map = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.non_empty_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_string(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.non_empty_string = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_string(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.non_empty_string = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_string(&self) -> &::std::option::Option<::std::string::String> {
    &self.non_empty_string
}
#[allow(missing_docs)] // documentation missing in model
pub fn one_to_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.one_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_one_to_ten(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.one_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_one_to_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.one_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.string_less_than_or_equal_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_string_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.string_less_than_or_equal_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_string_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::string::String> {
    &self.string_less_than_or_equal_to_ten
}
#[allow(missing_docs)] // documentation missing in model
pub fn that_ten_to_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i64>) -> Self {
    self.that_ten_to_ten = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_that_ten_to_ten(mut self, input: ::std::option::Option<::std::primitive::i64>) -> Self {
    self.that_ten_to_ten = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_that_ten_to_ten(&self) -> &::std::option::Option<::std::primitive::i64> {
    &self.that_ten_to_ten
}
    /// Consumes the builder and constructs a [`GetConstraintsOutput`](crate::operation::operation::GetConstraintsOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_constraints::GetConstraintsOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_constraints::GetConstraintsOutput {
            blob_less_than_or_equal_to_ten: self.blob_less_than_or_equal_to_ten,
greater_than_one: self.greater_than_one,
less_than_ten: self.less_than_ten,
list_less_than_or_equal_to_ten: self.list_less_than_or_equal_to_ten,
map_less_than_or_equal_to_ten: self.map_less_than_or_equal_to_ten,
my_blob: self.my_blob,
my_list: self.my_list,
my_list_of_utf8_bytes: self.my_list_of_utf8_bytes,
my_map: self.my_map,
my_string: self.my_string,
my_utf8_bytes: self.my_utf8_bytes,
non_empty_blob: self.non_empty_blob,
non_empty_list: self.non_empty_list,
non_empty_map: self.non_empty_map,
non_empty_string: self.non_empty_string,
one_to_ten: self.one_to_ten,
string_less_than_or_equal_to_ten: self.string_less_than_or_equal_to_ten,
that_ten_to_ten: self.that_ten_to_ten,
        })
    }
}
