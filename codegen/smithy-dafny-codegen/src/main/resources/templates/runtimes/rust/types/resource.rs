
pub trait $rustResourceName:L {
  $resourceOperations:L
}

#[derive(::std::clone::Clone)]
pub struct $rustResourceName:LRef {
  pub inner: ::std::rc::Rc<std::cell::RefCell<dyn $rustResourceName:L>>
}

impl ::std::cmp::PartialEq for $rustResourceName:LRef {
    fn eq(&self, other: &$rustResourceName:LRef) -> bool {
        ::std::rc::Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl ::std::fmt::Debug for $rustResourceName:LRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<$rustResourceName:LRef>")
    }
}

$operationModules:L