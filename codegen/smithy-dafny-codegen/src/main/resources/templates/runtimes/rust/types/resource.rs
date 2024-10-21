
$rustResourceComment:L
pub trait $rustResourceName:L {
  $resourceOperations:L
}

#[derive(::std::clone::Clone)]
/// A reference to a $rustResourceName:L
pub struct $rustResourceName:LRef {
  pub inner: ::std::rc::Rc<std::cell::RefCell<dyn $rustResourceName:L>>
}

impl<T : $rustResourceName:L + 'static> From<T> for $rustResourceName:LRef {
    fn from(value: T) -> Self {
        Self { inner: std::rc::Rc::new(std::cell::RefCell::new(value)) }
    }
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
