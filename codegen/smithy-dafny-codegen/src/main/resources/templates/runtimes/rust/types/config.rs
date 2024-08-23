#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct $configName:L {}

impl $configName:L {
    pub fn builder() -> $configName:LBuilder {
        $configName:LBuilder::new()
    }
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct $configName:LBuilder {}

impl $configName:LBuilder {
    /// Creates a new `$configName:LBuilder`.
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub fn build(
        self,
    ) -> ::std::result::Result<$configName:L, ::aws_smithy_types::error::operation::BuildError>
    {
        ::std::result::Result::Ok($configName:L {})
    }
}