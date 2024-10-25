#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
$rustUnionComment:L
pub enum $rustUnionName:L {
    $variants:L
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
impl $rustUnionName:L {
    $asImpls:L
    $isImpls:L
    /// Returns true if the enum instance is the `Unknown` variant.
    pub fn is_unknown(&self) -> ::std::primitive::bool {
        matches!(self, Self::Unknown)
    }
}
