
$rustResourceComment:L
pub trait $rustResourceName:L : Send + Sync {
  $resourceOperations:L
}

#[derive(::std::clone::Clone)]
/// A reference to a $rustResourceName:L
pub struct $rustResourceName:LRef {
  pub inner: ResourceInner<dyn $rustResourceName:L>
}

/// A wrapper around Rc (or Arc with the `sync` feature) that provides a no-op .lock() method for backwards compatibility.
/// 
/// Since the trait requires Send + Sync, no actual locking is needed - the inner value
/// is already thread-safe. The .lock() method simply returns a guard that derefs to the inner value.
pub struct ResourceInner<T: ?Sized>(::dafny_runtime::Rc<T>);

impl<T: ?Sized> Clone for ResourceInner<T> {
    fn clone(&self) -> Self {
        ResourceInner(self.0.clone())
    }
}

impl<T: ?Sized> ResourceInner<T> {
    /// Returns a guard providing access to the inner resource.
    /// 
    /// This method exists for backwards compatibility with code that used the old
    /// Mutex-based API. No actual locking occurs - the guard simply provides access
    /// to the inner Arc.
    #[inline]
    pub fn lock(&self) -> Result<ResourceGuard<'_, T>, ::std::convert::Infallible> {
        Ok(ResourceGuard(&self.0))
    }

    /// Compares two ResourceInner pointers for equality.
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        ::dafny_runtime::Rc::ptr_eq(&self.0, &other.0)
    }
}

impl ResourceInner<dyn $rustResourceName:L> {
    /// Creates a new ResourceInner wrapping the given value.
    pub fn new<T: $rustResourceName:L + 'static>(value: T) -> Self {
        ResourceInner(::dafny_runtime::Rc::new(value) as ::dafny_runtime::Rc<dyn $rustResourceName:L>)
    }
}

impl<T: ?Sized> ::std::ops::Deref for ResourceInner<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A guard that provides access to a resource. Returned by ResourceInner::lock().
/// 
/// Unlike MutexGuard, this does not actually hold a lock - it simply provides
/// a reference to the underlying resource.
pub struct ResourceGuard<'a, T: ?Sized>(&'a ::dafny_runtime::Rc<T>);

impl<T: ?Sized> ::std::ops::Deref for ResourceGuard<'_, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> ::std::fmt::Debug for ResourceInner<T> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "ResourceInner(...)")
    }
}

impl<T: ?Sized> ::std::fmt::Debug for ResourceGuard<'_, T> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "ResourceGuard(...)")
    }
}

impl<T : $rustResourceName:L + 'static> From<T> for $rustResourceName:LRef {
    fn from(value: T) -> Self {
        Self { inner: ResourceInner::new(value) }
    }
}

impl ::std::cmp::PartialEq for $rustResourceName:LRef {
    fn eq(&self, other: &$rustResourceName:LRef) -> bool {
        self.inner.ptr_eq(&other.inner)
    }
}

impl ::std::fmt::Debug for $rustResourceName:LRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<$rustResourceName:LRef>")
    }
}

$operationModules:L
