#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
$rustStructureComment:L
pub struct $rustStructureName:L {
    $fields:L
}
impl $rustStructureName:L {
    $getters:L
}
impl $rustStructureName:L {
    /// Creates a new builder-style object to manufacture [`$rustStructureName:L`]($qualifiedRustStructureType:L).
    pub fn builder() -> $rustTypesModuleName:L::builders::$rustStructureName:LBuilder {
        $rustTypesModuleName:L::builders::$rustStructureName:LBuilder::default()
    }
}

/// A builder for [`$rustStructureName:L`]($qualifiedRustStructureType:L).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct $rustStructureName:LBuilder {
    $builderFields:L
}
impl $rustStructureName:LBuilder {
    $builderAccessors:L
    /// Consumes the builder and constructs a [`$rustStructureName:L`]($qualifiedRustStructureType:L).
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
