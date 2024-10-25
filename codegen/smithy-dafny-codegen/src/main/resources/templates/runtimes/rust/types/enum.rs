#[derive(Debug, PartialEq, Copy, Clone)]
$rustEnumComment:L
pub enum $rustEnumName:L {
    $variants:L
}

impl ::std::fmt::Display for $rustEnumName:L {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            $displayVariants:L
        }
    }
}
