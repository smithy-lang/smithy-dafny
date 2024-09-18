#[allow(dead_code)]
pub fn to_dafny(
    value: &$rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef,
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
  obj: $rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef,
}

impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any> for $rustResourceName:LWrapper {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<
      dyn crate::r#$dafnyTypesModuleName:L::$dafnyResourceName:L,
    >,
) -> $rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef {
    let wrap = $dafnyResourceName:LDafnyWrapper {
        obj: dafny_value.clone(),
    };
    $rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef {
      inner: ::std::rc::Rc::new(::std::cell::RefCell::new(wrap))
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct $dafnyResourceName:LDafnyWrapper {
  pub(crate) obj: ::dafny_runtime::Object<
      dyn crate::r#$dafnyTypesModuleName:L::$dafnyResourceName:L,
  >,
}

impl crate::$dafnyTypesModuleName:L::$dafnyResourceName:L
  for $rustResourceName:LWrapper
{
  $resourceWrapperOperations:L
}

impl $rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:L for $dafnyResourceName:LDafnyWrapper 
{
  $resourceDafnyWrapperOperations:L
}