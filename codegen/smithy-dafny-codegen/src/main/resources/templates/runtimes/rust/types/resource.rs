
$rustResourceComment:L
pub trait $rustResourceName:L : Send + Sync {
  $resourceOperations:L
}

#[derive(::std::clone::Clone)]
/// A reference to a $rustResourceName:L
pub struct $rustResourceName:LRef {
  pub inner: ::dafny_runtime::Rc<::dafny_runtime::RefCell<dyn $rustResourceName:L>>
}

impl<T : $rustResourceName:L + 'static> From<T> for $rustResourceName:LRef {
    fn from(value: T) -> Self {
        Self { inner: dafny_runtime::Rc::new(::dafny_runtime::RefCell::new(value)) }
    }
}

impl ::std::cmp::PartialEq for $rustResourceName:LRef {
    fn eq(&self, other: &$rustResourceName:LRef) -> bool {
        ::dafny_runtime::Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl ::std::fmt::Debug for $rustResourceName:LRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<$rustResourceName:LRef>")
    }
}

$operationModules:L
