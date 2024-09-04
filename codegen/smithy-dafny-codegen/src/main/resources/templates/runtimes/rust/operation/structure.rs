#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct $rustStructureName:L {
    $fields:L
}
impl $rustStructureName:L {
    $getters:L
}
impl $rustStructureName:L {
    /// Creates a new builder-style object to manufacture [`$rustStructureName:L`](crate::operation::operation::$rustStructureName:L).
    pub fn builder() -> crate::operation::$snakeCaseOperationName:L::builders::$rustStructureName:LBuilder {
        crate::operation::$snakeCaseOperationName:L::builders::$rustStructureName:LBuilder::default()
    }
}

/// A builder for [`$rustStructureName:L`](crate::operation::operation::$rustStructureName:L).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct $rustStructureName:LBuilder {
    $builderFields:L
}
impl $rustStructureName:LBuilder {
    $builderAccessors:L
    /// Consumes the builder and constructs a [`$rustStructureName:L`](crate::operation::operation::$rustStructureName:L).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$rustStructureName:L,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::$snakeCaseOperationName:L::$rustStructureName:L {
            $builderAssignments:L
        })
    }
}