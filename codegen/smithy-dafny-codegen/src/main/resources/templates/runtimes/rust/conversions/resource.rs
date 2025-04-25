#[allow(dead_code)]
pub fn to_dafny(
    value: &$rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef,
) -> ::dafny_runtime::Object<
  dyn crate::r#$dafnyTypesModuleName:L::$dafnyResourceName:L,
> {
  let wrap = $rustResourceName:LWrapper {
      obj: value.clone(),
  };
  let inner = ::dafny_runtime::Rc::new(::dafny_runtime::UnsafeCell::new(wrap));
  ::dafny_runtime::Object (Some(inner) )
}

pub struct $rustResourceName:LWrapper {
  obj: $rustTypesModuleName:L::$snakeCaseResourceName:L::$rustResourceName:LRef,
}

impl ::dafny_runtime::UpcastObject<::dafny_runtime::DynAny> for $rustResourceName:LWrapper {
  ::dafny_runtime::UpcastObjectFn!(::dafny_runtime::DynAny);
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
      inner: ::dafny_runtime::Rc::new(::dafny_runtime::RefCell::new(wrap))
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