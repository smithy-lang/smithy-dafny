
pub trait $rustResourceName:L {
  $resourceOperations:L
}

pub type $rustResourceName:LRef = ::std::rc::Rc<std::cell::RefCell<dyn $rustResourceName:L>>;
