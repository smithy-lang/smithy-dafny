#![allow(
    deprecated,
    non_upper_case_globals,
    unused,
    non_snake_case,
    non_camel_case_types
)]

pub mod client;
pub mod conversions;
pub mod deps;
pub(crate) mod implementation_from_dafny;
/// Common errors and error handling utilities.
pub mod kms;
/// All operations that this crate can perform.
mod standard_library_conversions;
mod standard_library_externs;
pub mod types;
pub(crate) use crate::implementation_from_dafny::_Wrappers_Compile;
pub use crate::implementation_from_dafny::software;
pub use client::Client;
