#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
$rustStructureComment:L
pub struct $configName:L {
    $fields:L
}
impl $configName:L {
    $getters:L
}
impl $configName:L {
    /// Creates a new builder-style object to manufacture [`$configName:L`]($qualifiedRustStructureType:L).
    pub fn builder() -> $rustTypesModuleName:L::$snakeCaseStructureName:L::$configName:LBuilder {
        $rustTypesModuleName:L::$snakeCaseStructureName:L::$configName:LBuilder::default()
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
        $rustTypesModuleName:L::$snakeCaseStructureName:L::$configName:L,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok($rustTypesModuleName:L::$snakeCaseStructureName:L::$configName:L {
            $builderAssignments:L
        })
    }
}
