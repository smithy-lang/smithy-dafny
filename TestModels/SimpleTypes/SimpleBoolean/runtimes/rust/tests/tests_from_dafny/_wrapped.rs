use std::any::Any;

use crate::tests_from_dafny::*;
use aws_smithy_types::error::operation::BuildError;
use dafny_runtime::UpcastObject;
use simple_boolean::*;
use tokio::runtime::Runtime;

struct WrappedClient {
    wrapped: Client,

    /// A `current_thread` runtime for executing operations on the
    /// asynchronous client in a blocking manner.
    rt: Runtime
}

impl UpcastObject<dyn Any> for WrappedClient {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient
    for WrappedClient
{
    fn GetBoolean(
        &mut self,
        input: &std::rc::Rc<
            ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanInput,
        >,
    ) -> std::rc::Rc<
        ::simple_boolean_dafny::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput,
            >,
            std::rc::Rc<::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_boolean::_get_boolean_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_boolean::GetBoolean::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                ::simple_boolean_dafny::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_boolean::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                ::simple_boolean_dafny::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_boolean::_get_boolean_output::to_dafny(client),
                },
            ),
        }
    }
}

impl r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default {
    pub fn WrappedSimpleBoolean(config: &::std::rc::Rc<
        ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig,
    >) -> ::std::rc::Rc<::simple_boolean_dafny::r#_Wrappers_Compile::Result<
            ::dafny_runtime::Object<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
            ::std::rc::Rc<::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>
    >>{
        let rt_result = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build();
        if rt_result.is_err() {
        return ::std::rc::Rc::new(to_opaque_error_result(rt_result.err().unwrap()));
        }
        let rt = rt_result.unwrap();
        let result = Client::from_conf(
            simple_boolean::conversions::simple_boolean_config::_simple_boolean_config::from_dafny(
                config.clone(),
            ),
        );
        match result {
            Err(error) => {
                let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> =
                    ::dafny_runtime::Object(Some(::std::rc::Rc::new(
                        ::std::cell::UnsafeCell::new(error),
                    )));
                ::std::rc::Rc::new(
                    ::simple_boolean_dafny::_Wrappers_Compile::Result::Failure {
                        error: ::std::rc::Rc::new(
                            ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error::Opaque {
                                obj: error_obj,
                            },
                        ),
                    },
                )
            }
            Ok(client) => {
                let wrap = WrappedClient {
                    wrapped: client.clone(),
                    rt
                };
                let inner: ::std::rc::Rc<::std::cell::UnsafeCell<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>>
                    = ::std::rc::Rc::new(::std::cell::UnsafeCell::new(wrap));

                ::std::rc::Rc::new(
                    ::simple_boolean_dafny::_Wrappers_Compile::Result::Success {
                        value: ::dafny_runtime::Object(Some(inner)),
                    },
                )
            }
        }
    }
}

fn to_opaque_error_result(error: std::io::Error) -> ::simple_boolean_dafny::r#_Wrappers_Compile::Result<
::dafny_runtime::Object<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
::std::rc::Rc<::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>
> {
  let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> =
      ::dafny_runtime::Object(Some(::std::rc::Rc::new(
          ::std::cell::UnsafeCell::new(error),
      )));
      simple_boolean_dafny::_Wrappers_Compile::Result::Failure {
        error: ::std::rc::Rc::new(
            ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error::Opaque {
                obj: error_obj,
            },
        ),
    }
}