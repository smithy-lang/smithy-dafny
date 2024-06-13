// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetResourceDataInput {
    pub(crate) blobValue: Option<Vec<u8>>,
    pub(crate) booleanValue: Option<bool>,
    pub(crate) stringValue: Option<String>,
    pub(crate) integerValue: Option<i32>,
    pub(crate) longValue: Option<i64>,
}

impl GetResourceDataInput {
    #[allow(missing_docs)] // documentation missing in model
    pub fn blobValue(&self) -> &Option<Vec<u8>> {
        &self.blobValue
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn booleanValue(&self) -> Option<bool> {
        self.booleanValue
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn stringValue(&self) -> &Option<String> {
        &self.stringValue
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn integerValue(&self) -> Option<i32> {
        self.integerValue
    }
    #[allow(missing_docs)] // documentation missing in model
    pub fn longValue(&self) -> Option<i64> {
        self.longValue
    }
}

impl GetResourceDataInput {
    /// Creates a new builder-style object to manufacture [`GetResourceDataInput`](crate::operation::operation::GetResourceDataInput).
    pub fn builder() -> crate::operation::get_resource_data::builders::GetResourceDataInputBuilder {
        crate::operation::get_resource_data::builders::GetResourceDataInputBuilder::default()
    }
}

/// A builder for [`GetResourceDataInput`](crate::operation::operation::GetResourceDataInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetResourceDataInputBuilder {
    blobValue: Option<Vec<u8>>,
    booleanValue: Option<bool>,
    stringValue: Option<String>,
    integerValue: Option<i32>,
    longValue: Option<i64>,
}

impl GetResourceDataInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
    pub fn blobValue(mut self, input: Vec<u8>) -> Self {
        self.blobValue = Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_blobValue(mut self, input: Option<Vec<u8>>) -> Self {
        self.blobValue = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_blobValue(&self) -> &Option<Vec<u8>> {
        &self.blobValue
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn booleanValue(mut self, input: bool) -> Self {
        self.booleanValue = Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_booleanValue(mut self, input: Option<bool>) -> Self {
        self.booleanValue = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_booleanValue(&self) -> Option<bool> {
        self.booleanValue
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn stringValue(mut self, input: String) -> Self {
        self.stringValue = Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_stringValue(mut self, input: Option<String>) -> Self {
        self.stringValue = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_stringValue(&self) -> &Option<String> {
        &self.stringValue
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn integerValue(mut self, input: i32) -> Self {
        self.integerValue = Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_integerValue(mut self, input: Option<i32>) -> Self {
        self.integerValue = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_integerValue(&self) -> Option<i32> {
        self.integerValue
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn longValue(mut self, input: i64) -> Self {
        self.longValue = Some(input);
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn set_longValue(mut self, input: Option<i64>) -> Self {
        self.longValue = input;
        self
    }

    #[allow(missing_docs)] // documentation missing in model
    pub fn get_longValue(&self) -> Option<i64> {
        self.longValue
    }

    /// Consumes the builder and constructs a [`GetResourceDataInput`](crate::operation::operation::GetResourceDataInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resource_data::GetResourceDataInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resource_data::GetResourceDataInput {
            blobValue: self.blobValue,
            booleanValue: self.booleanValue,
            stringValue: self.stringValue,
            integerValue: self.integerValue,
            longValue: self.longValue,
        })
    }
}
