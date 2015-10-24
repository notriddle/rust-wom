// Copyright 2015 Michael Howell <michael@notriddle.com>
// Copyright 2015 whataloadofwhat
//
// This library is released under the same terms as Rust itself.

//! Write-only memory, suitable for use in things like memory-mapped device
//! drivers.
//!
//! The owner of a `Wom<T>` can read from it, as long as there are no
//! outstanding references to it. Presumably, the value needs to be read
//! at some point to be usable, and this is consistent with Rust's usual
//! ownership and borrowing semantics. It is never considered safe to read
//! the value while a write-only reference exists.
//!
//! A `&mut Wom<T>` (a write-only exclusive reference) can be created directly
//! from a `&mut T`; this will extend the borrow, preventing the underlying `T`
//! from being read as long as the write-only reference exists. This is not
//! safe for a `&T` to a `&Wom<T>`, to prevent having write-only references
//! and readable references coexisting (&Wom<T> is useless except when T is
//! a `Cell<_>` anyway).

use std::{ptr, ops};
use std::cell::Cell;

#[repr(C)]
pub struct Wom<T: ?Sized>(T);

// The correct bounds are !Drop, but that ain't possible right now.
impl<T: Copy> Wom<T> {
    /// Create a owned write-only value.
    ///
    /// # Example
    /// ```
    /// # use wom::Wom;
    /// let mut k = Wom::new(3);
    /// k.set(5);
    /// assert_eq!(5, k.into_inner());
    /// ```
    pub fn new(x: T) -> Self {
        Wom(x)
    }
    /// Convert a owned write-only value into a owned readable value.
    pub fn into_inner(self) -> T {
        self.0
    }
    /// Allow aliasing the mutable reference, using a `Cell`.
    /// 
    /// # Example
    /// ```
    /// # use wom::Wom;
    /// let mut m = Wom::new(42);
    /// {
    ///     let n = m.cell();
    ///     let p = n;
    ///     n.set_cell(0);
    ///     p.set_cell(69);
    /// }
    /// assert_eq!(m.into_inner(), 69);
    /// ```
    pub fn cell(&mut self) -> &Wom<Cell<T>> {
         unsafe {
            &mut *(self as *mut Self as *mut Wom<Cell<T>>)
        }
    }
}

impl<T> Wom<T> {
    /// Set the value pointed to by a write-only reference.
    pub fn set(&mut self, val: T) {
        unsafe { ptr::write(&mut self.0, val) };
    }
}

impl<T: ?Sized> Wom<T> {
    /// Create an exclusive write-only reference from an exclusive reference.
    /// 
    /// # Example
    /// ```
    /// # use wom::Wom;
    /// let mut k = 3;
    /// {
    ///     let mut w_k = Wom::from_ref_mut(&mut k);
    ///     w_k.set(5);
    /// }
    /// assert_eq!(k, 5);
    /// ```
    pub fn from_ref_mut<'a>(x: &'a mut T) -> &'a mut Self {
        unsafe {
            &mut *(x as *mut T as *mut Self)
        }
    }
    /// Get a shared `Wom<T>`. This is useless except when used with a
    /// `&Cell<_>`, and it is unsound to read a value while there are
    /// write-only references to it.
    pub unsafe fn from_ref<'a>(x: &'a T) -> &'a Self {
        & *(x as *const T as *const Self)
    }
    /// Get an exclusive readable reference to the underlying value.
    pub unsafe fn unwrap_mut(&mut self) -> &mut T {
        &mut self.0
    }
    /// Get a shared readable reference to the underlying value.
    pub unsafe fn unwrap(&self) -> &T {
        &self.0
    }
}

impl<T: Copy> Wom<Cell<T>> {
    /// Mutate a write-only `Cell`. Due to the presence of a reference count,
    /// this cannot be implemented for a `RefCell`.
    ///
    /// # Example
    /// ```
    /// # use wom::Wom;
    /// use std::cell::Cell;
    /// let mut k = Cell::new(3);
    /// {
    ///     let m_k = &*Wom::from_ref_mut(&mut k);
    ///     let l = m_k;
    ///     let m = m_k;
    ///     l.set_cell(3);
    ///     m.set_cell(5);
    /// }
    /// assert_eq!(k.get(), 5);
    /// ```
    pub fn set_cell(&self, val: T) {
        self.0.set(val);
    }
}

/// Access a member variable of a value in a write-only shared reference.
///
/// # Example
/// ```
/// #[macro_use] extern crate wom;
/// # use wom::Wom;
/// # fn main() {
/// use std::cell::Cell;
/// struct K {
///     inner: Cell<usize>,
/// }
/// let mut k = K{ inner: Cell::new(3) };
/// {
///     let m_k = &*Wom::from_ref_mut(&mut k);
///     let inner_k = wom!(m_k, inner);
///     inner_k.set_cell(5);
/// }
/// assert_eq!(k.inner.get(), 5);
/// # }
/// ```
#[macro_export]
macro_rules! wom {
    ($wom:expr, $member:ident) => {
        unsafe { $crate::Wom::from_ref(&$crate::Wom::unwrap($wom).$member) }
    }
}

/// Access a member variable of a value in a write-only exclusive reference.
///
/// # Example
/// ```
/// #[macro_use] extern crate wom;
/// # use wom::Wom;
/// # fn main() {
/// struct K {
///     inner: usize,
/// }
/// let mut k = K{ inner: 3 };
/// {
///     let m_k = Wom::from_ref_mut(&mut k);
///     let mut inner_k = wom_mut!(m_k, inner);
///     inner_k.set(5);
/// }
/// assert_eq!(k.inner, 5);
/// # }
/// ```
#[macro_export]
macro_rules! wom_mut {
    ($wom:expr, $member:ident) => {
        unsafe { $crate::Wom::from_ref_mut(&mut $crate::Wom::unwrap_mut($wom).$member) }
    }
}

/// An iterator over the contents of a write-only shared slice.
/// 
/// # Example
/// ```
/// # use wom::Wom;
/// use std::cell::Cell;
/// let mut k = [Cell::new(1), Cell::new(1), Cell::new(1), Cell::new(1)];
/// {
///     let k_v = &*Wom::from_ref_mut(&mut k[..]);
///     for i in (1..).zip(k_v.into_iter()) {
///         i.1.set_cell(i.0);
///     }
/// }
/// assert_eq!(&k[0].get(), &1);
/// assert_eq!(&k[1].get(), &2);
/// assert_eq!(&k[2].get(), &3);
/// assert_eq!(&k[3].get(), &4);
/// ```
pub struct WomIter<'a, T: 'a> (::std::slice::Iter<'a, T>);

impl<'a, T: 'a> Iterator for WomIter<'a, T> {
    type Item = &'a Wom<T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|x| unsafe { Wom::from_ref(x) })
    }
}

impl<'a, T: 'a> ::std::iter::IntoIterator for &'a Wom<[T]> {
    type IntoIter = WomIter<'a, T>;
    type Item = &'a Wom<T>;
    fn into_iter(self) -> Self::IntoIter {
        WomIter((&self.0).into_iter())
    }
}

/// An iterator over the contents of a write-only shared slice.
/// 
/// # Example
/// ```
/// # use wom::Wom;
/// let mut k = [1; 4];
/// {
///     let k_v = Wom::from_ref_mut(&mut k[..]);
///     for i in (1..).zip(k_v.into_iter()) {
///         i.1.set(i.0);
///     }
/// }
/// assert_eq!(&k[0], &1);
/// assert_eq!(&k[1], &2);
/// assert_eq!(&k[2], &3);
/// assert_eq!(&k[3], &4);
/// ```

pub struct WomIterMut<'a, T: 'a> (::std::slice::IterMut<'a, T>);

impl<'a, T: 'a> Iterator for WomIterMut<'a, T> {
    type Item = &'a mut Wom<T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Wom::from_ref_mut)
    }
}

impl<'a, T: 'a> ::std::iter::IntoIterator for &'a mut Wom<[T]> {
    type IntoIter = WomIterMut<'a, T>;
    type Item = &'a mut Wom<T>;
    fn into_iter(mut self) -> Self::IntoIter {
        WomIterMut((&mut self.0).into_iter())
    }
}

impl<T, U> ops::Index<U> for Wom<[T]> where [T]: ops::Index<U> {
    type Output = Wom<<[T] as ops::Index<U>>::Output>;
    fn index(&self, idx: U) -> &Self::Output {
        unsafe { Wom::from_ref(&self.unwrap()[idx]) }
    }
}

impl<T, U> ops::IndexMut<U> for Wom<[T]> where [T]: ops::IndexMut<U> {
    fn index_mut(&mut self, idx: U) -> &mut Self::Output {
        unsafe { Wom::from_ref_mut(&mut self.unwrap_mut()[idx]) }
    }
}

impl<T: Copy> Wom<[T]> {
    /// Allow aliasing the mutable reference, using a slice of `Cell`s.
    ///
    /// # Example
    /// ```
    /// # use wom::Wom;
    /// let mut k = [42, 69];
    /// {
    ///     let m = Wom::from_ref_mut(&mut k[..]);
    ///     let n = m.cell_slice();
    ///     let p = n;
    ///     n[0].set_cell(3);
    ///     p[1].set_cell(1);
    /// }
    /// assert_eq!(k, [3, 1]);
    /// ```
    pub fn cell_slice(&mut self) -> &Wom<[Cell<T>]> {
         unsafe {
            &mut *(self as *mut Self as *mut Wom<[Cell<T>]>)
        }
    }

}

#[cfg(test)]
mod test {
    use super::*;
    use std::cell::Cell;
    #[test]
    fn test_idx() {
        let mut k = [ Cell::new(3) ];
        {
            let w_k = &*Wom::from_ref_mut(&mut k[..]);
            &w_k[0].set_cell(5);
        }
        assert_eq!(&k[0].get(), &5);
    }
    #[test]
    fn test_idx_mut() {
        let mut k = [ 3 ];
        {
            let w_k = Wom::from_ref_mut(&mut k[..]);
            &w_k[0].set(5);
        }
        assert_eq!(&k[0], &5);
    }
}
