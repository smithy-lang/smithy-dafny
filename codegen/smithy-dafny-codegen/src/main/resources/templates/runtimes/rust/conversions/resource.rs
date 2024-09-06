#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::$snakeCaseResourceName:L::$rustResourceName:LRef,
) -> ::dafny_runtime::Object<
  dyn crate::r#$dafnyTypesModuleName:L::$dafnyResourceName:L,
> {
  let wrap = $rustResourceName:LWrapper {
      obj: value.clone(),
  };
  let inner = ::std::rc::Rc::new(::std::cell::UnsafeCell::new(wrap));
  ::dafny_runtime::Object (Some(inner) )
}

pub struct $rustResourceName:LWrapper {
  obj: crate::types::$snakeCaseResourceName:L::$rustResourceName:LRef,
}

impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any> for $rustResourceName:LWrapper {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<
      dyn crate::r#$dafnyTypesModuleName:L::ISimpleResource,
    >,
) -> crate::types::$snakeCaseResourceName:L::$rustResourceName:LRef {
    let wrap = $dafnyResourceName:LDafnyWrapper {
        obj: dafny_value.clone(),
    };
    ::std::rc::Rc::new(::std::cell::RefCell::new(wrap))
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct $dafnyResourceName:LDafnyWrapper {
  pub(crate) obj: ::dafny_runtime::Object<
      dyn crate::r#$dafnyTypesModuleName:L::$dafnyResourceName:L,
  >,
}

$resourceOperations:L