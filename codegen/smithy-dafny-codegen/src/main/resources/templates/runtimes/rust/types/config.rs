#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct $configName:L {
    $fields:L
}
impl $configName:L {
    $getters:L
}
impl $configName:L {
    /// Creates a new builder-style object to manufacture [`$configName:L`]($qualifiedRustStructureType:L).
    pub fn builder() -> crate::types::builders::$configName:LBuilder {
        crate::types::builders::$configName:LBuilder::default()
    }
}

/// A builder for [`$configName:L`]($qualifiedRustStructureType:L).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct $configName:LBuilder {
    $builderFields:L
}
impl $configName:LBuilder {
    $builderAccessors:L
    /// Consumes the builder and constructs a [`$configName:L`]($qualifiedRustStructureType:L).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        $qualifiedRustStructureType:L,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok($qualifiedRustStructureType:L {
            $builderAssignments:L
        })
    }
}
