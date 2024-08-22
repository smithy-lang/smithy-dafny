// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

#[derive(Clone, Debug)]
pub struct Object(pub Option<::std::rc::Rc<std::cell::UnsafeCell<dyn ::std::any::Any>>>);

#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    SimpleErrorsException {
        message: String,
    },
    CollectionOfErrors {
        list: Vec<Error>,
        message: String,
    },
    Opaque {
        // obj: Option<::std::rc::Rc<std::cell::UnsafeCell<dyn ::std::any::Any>>>,
        obj: Object,
    },
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        if let Some(p) = &self.0 {
            if let Some(q) = &other.0 {
                // To compare addresses, we need to ensure we only compare thin pointers
                // https://users.rust-lang.org/t/comparing-addresses-between-fat-and-thin-pointers/89008
                ::std::ptr::eq(p.as_ref().get() as *const (), q.as_ref().get() as *const ())
            } else {
                false
            }
        } else {
            false
        }
    }
}

impl Eq for Error {}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ::std::error::Error for Error {}