#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    $modeledErrorVariants:L
    Opaque {
        obj: ::dafny_runtime::Object<dyn ::std::any::Any>,
    },
}

impl ::std::cmp::Eq for Error {}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ::std::error::Error for Error {}
