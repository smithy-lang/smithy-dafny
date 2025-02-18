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
/// Common errors and error handling utilities.
pub mod error;
pub mod factory;
pub(crate) mod implementation_from_dafny;
/// All operations that this crate can perform.
pub mod operation;
mod standard_library_conversions;
mod standard_library_externs;
pub mod types;
pub mod validation;
pub mod wrapped;
pub(crate) use crate::implementation_from_dafny::_SimpleExtendableResourcesTest_Compile;
pub(crate) use crate::implementation_from_dafny::_WrappedTest_Compile;
pub(crate) use crate::implementation_from_dafny::_Wrappers_Compile;
pub(crate) use crate::implementation_from_dafny::simple;
pub use crate::types::simple_extendable_resources_config::SimpleExtendableResourcesConfig;
pub use client::Client;
