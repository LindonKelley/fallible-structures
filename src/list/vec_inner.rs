//! Inner parts of [crate::list::Vec]. Many things in here specify public visibility to prevent
//! private-in-public issues, but this file is not publicly exported and is not intended for external use,
//! changes to it will not constitute a breaking change.

// any uncommented unsafe function use can be assumed to be
// SAFETY: safety contract upheld by caller
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]

use core::{alloc::Layout, marker::PhantomData, mem::{ManuallyDrop, MaybeUninit}, ptr::NonNull, usize};

use crate::{alloc::{self, Allocator}, error::{AllocError, AllocLayoutError, FixedSizeAllocError, FixedSizeError}};

/// **Internal use, changes will not constitute a breaking change.**
/// 
/// Inner part of [crate::list::Vec], only deals with a vector of unintialized data and a capacity, users should implement proper
/// drop handling for types and must keep track of the allocator. May leak memory if [VecInner::dealloc] isn't called.
#[doc(hidden)]
pub struct VecInner<V: VecInnerWithoutCapacity> {
    inner: V,
    capacity: V::Capacity
}

impl <V: VecInnerWithoutCapacity> VecInner<V> {
    /// Constructs and returns a new instance. [VecInner::dealloc] should be called at the end of this instance's life or else it may
    /// leak memory.
    pub fn new() -> Self {
        let (inner, capacity) = V::new();
        Self { inner, capacity: V::Capacity::from_new(capacity) }
    }

    /// Attempts to increase the capacity to `grow_to`, implementations may exceed `grow_to` due to [Allocator::allocate] potentionally
    /// over-allocating. If `grow_to` <= capacity then this function simply returns Ok.
    /// 
    /// # Safety
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    pub unsafe fn grow_capacity(&mut self, grow_to: usize, alloc: &V::Allocator) -> Result<(), V::ReserveError> {
        let mut cap = self.capacity.get();
        let res = self.inner.grow_capacity(&mut cap, grow_to, alloc);
        if res.is_err() {
            debug_assert_eq!(cap, self.capacity.get());
        }
        self.capacity.set(cap);
        res
    }

    /// Attempts to shrink the capacity of this instance to just fit the provided `shrink_to`, may fail to shrink all the way.
    /// if `shrink_to` >= capacity then this function simply returns Ok.
    /// 
    /// # Safety
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    pub unsafe fn shrink_capacity(&mut self, shrink_to: usize, alloc: &V::Allocator) -> Result<(), V::ShrinkError> {
        let mut cap = self.capacity.get();
        let res = self.inner.shrink_capacity(&mut cap, shrink_to, alloc);
        self.capacity.set(cap);
        res
    }

    /// Returns a reference to the uninitialized slice of the underlying values, the length of this slice will be [VecInner::capacity]
    pub fn as_uninit_slice<'a>(&'a self) -> &'a [MaybeUninit<V::Item>] {
        unsafe {
            // SAFETY: ensured by this structure never modifying the capacities provided by the inner vec
            self.inner.as_uninit_slice(self.capacity.get())
        }
    }

    /// Returns a mutable reference to the uninitialized slice of the underlying values, the length of this slice will be [VecInner::capacity]
    pub fn as_uninit_slice_mut<'a>(&'a mut self) -> &'a mut [MaybeUninit<V::Item>] {
        unsafe {
            // SAFETY: ensured by this structure never modifying the capacities provided by the inner vec
            self.inner.as_uninit_slice_mut(self.capacity.get())
        }
    }

    /// Deallocates this instance, if this function is not called, memory leaks may occur.
    /// 
    /// # Safety
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    pub unsafe fn dealloc(self, alloc: &V::Allocator) {
        self.inner.dealloc(self.capacity.get(), alloc);
    }

    /// Returns the current capacity of this instance, if the item type is zero-sized, this is guaranteed to always return `usize::MAX`.
    pub fn capacity(&self) -> usize {
        self.capacity.get()
    }
}

/// **Internal use, changes will not constitute a breaking change.**
#[doc(hidden)]
pub trait Capacity<V> {
    fn from_new(new_cap: usize) -> Self;

    fn set(&mut self, cap: usize);

    fn get(&self) -> usize;
}

#[mutants::skip]
impl <T, A: Allocator, const IN_CAP: usize> Capacity<SmallVecInnerWithoutCapacity<T, A, IN_CAP>> for usize {
    fn from_new(new_cap: usize) -> Self {
        new_cap
    }

    fn set(&mut self, cap: usize) {
        *self = cap;
    }

    fn get(&self) -> usize {
        *self
    }
}

#[mutants::skip]
impl <T, A: Allocator, const CAP: usize> Capacity<InlineVecInnerWithoutCapacity<T, A, CAP>> for () {
    fn from_new(_new_cap: usize) -> Self {}

    fn set(&mut self, _cap: usize) {}

    fn get(&self) -> usize {
        if size_of::<T>() == 0 {
            usize::MAX
        } else {
            CAP
        }
    }
}

#[mutants::skip]
impl <T, A: Allocator> Capacity<AllocatingVecInnerWithoutCapacity<T, A>> for usize {
    fn from_new(new_cap: usize) -> Self {
        new_cap
    }

    fn set(&mut self, cap: usize) {
        *self = cap;
    }

    fn get(&self) -> usize {
        *self
    }
}

/// **Internal use, changes will not constitute a breaking change.**
/// 
/// Inner-most part of [crate::list::Vec], only deals with a vector of unintialized data, users should implement proper
/// drop handling for types and must keep track of the capacity and allocator. May leak memory if [VecInnerWithoutCapacity::dealloc]
/// isn't called.
#[doc(hidden)]
pub trait VecInnerWithoutCapacity: Sized {
    type Item;
    type Allocator: Allocator;
    type ReserveError;
    type ShrinkError;
    type Capacity: Capacity<Self>;

    /// Constructs and returns a new instance and the capacity, `cap`. Many interactions require a `cap` parameter, and this
    /// parameter must be consistent with interactions with this instance (no passing in any particular value). Users may choose
    /// to expose `cap` for informational reasons. The value of `cap` is guaranteed to always be `usize::MAX` when [VecInnerWithoutCapacity::Item] is
    /// zero-sized. [VecInnerWithoutCapacity::dealloc] should be called at the end of this instance's life or else it may leak memory.
    fn new() -> (Self, usize);

    /// Attempts to increase the capacity to `grow_to`, implementations may exceed `grow_to` due to [Allocator::allocate] potentionally
    /// over-allocating. If returning Ok, then the provided `cap` will be modified to reflect the changed capacity. If `grow_to` <= `cap`
    /// then this function simply returns Ok.
    /// 
    /// # Safety
    /// * The provided `cap` must be consistent with interactions with this instance, implementations are free to make 
    /// soundness decisions based on this requirement.
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    unsafe fn grow_capacity(&mut self, cap: &mut usize, grow_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ReserveError>;

    /// Attempts to shrink the capacity of this instance to just fit the provided `shrink_to`, may fail to shrink all the way.
    /// If returning Ok, then the provided `cap` will be modified to reflect the changed capacity. If `shrink_to` >= `cap` then
    /// this function simply returns Ok.
    /// 
    /// # Safety
    /// * The provided `cap` must be consistent with interactions with this instance, implementations are free to make 
    /// soundness decisions based on this requirement.
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    unsafe fn shrink_capacity(&mut self, cap: &mut usize, shrink_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ShrinkError>;

    /// Returns a reference to the uninitialized slice of the underlying values, the length of this slice will be the provided `cap`.
    /// 
    /// # Safety
    /// * The provided `cap` must be consistent with interactions with this instance, implementations are free to make 
    /// soundness decisions based on this requirement.
    unsafe fn as_uninit_slice<'a>(&'a self, cap: usize) -> &'a [MaybeUninit<Self::Item>];

    /// Returns a mutable reference to the uninitialized slice of the underlying values, the length of this slice will be the provided `cap`.
    /// 
    /// # Safety
    /// * The provided `cap` must be consistent with interactions with this instance, implementations are free to make 
    /// soundness decisions based on this requirement.
    unsafe fn as_uninit_slice_mut<'a>(&'a mut self, cap: usize) -> &'a mut [MaybeUninit<Self::Item>];

    /// Deallocates this instance, if this function is not called, memory leaks may occur.
    /// 
    /// # Safety
    /// * The provided `cap` must be consistent with interactions with this instance, implementations are free to make 
    /// soundness decisions based on this requirement.
    /// * The provided `alloc` must always be the same one used when interacting with this instance.
    unsafe fn dealloc(self, cap: usize, alloc: &Self::Allocator);
}

/// **Internal use, changes will not constitute a breaking change.**
#[doc(hidden)]
pub union SmallVecInnerWithoutCapacity<T, A: Allocator, const IN_CAP: usize> {
    inline: ManuallyDrop<InlineVecInnerWithoutCapacity<T, A, IN_CAP>>,
    allocated: ManuallyDrop<AllocatingVecInnerWithoutCapacity<T, A>>
}

impl <T, A: Allocator, const IN_CAP: usize> VecInnerWithoutCapacity for SmallVecInnerWithoutCapacity<T, A, IN_CAP> {
    type Item = T;

    type Allocator = A;

    type ReserveError = AllocLayoutError;

    type ShrinkError = FixedSizeAllocError;

    type Capacity = usize;

    fn new() -> (Self, usize) {
        let (inner_inline, cap) = InlineVecInnerWithoutCapacity::new();
        let s = Self { inline: ManuallyDrop::new(inner_inline) };
        debug_assert!(s.is_inline(cap));
        (s, cap)
    }

    unsafe fn grow_capacity(&mut self, cap: &mut usize, grow_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ReserveError> {
        if size_of::<T>() == 0 {
            debug_assert_eq!(*cap, usize::MAX);
            return Err(alloc::AllocError.into());
        }
        if self.is_inline(*cap) {
            if self.is_inline(grow_to) {
                // SAFETY: will never fail, this will only be reached if T is zero-sized or additional is 0
                // this function is here as a sanity check through MIRI, and should compile out entirely
                Ok(())
            } else {
                let (mut allocated, mut new_cap) = AllocatingVecInnerWithoutCapacity::new();
                allocated.grow_capacity(&mut new_cap, grow_to, alloc)?;
                core::ptr::copy_nonoverlapping(self.inline.as_uninit_slice(*cap).as_ptr(), allocated.as_uninit_slice_mut(*cap).as_mut_ptr(), *cap);
                *cap = new_cap;
                *self.allocated = allocated;
                Ok(())
            }
        } else {
            self.allocated.grow_capacity(cap, grow_to, alloc)
        }
    }

    unsafe fn shrink_capacity(&mut self, cap: &mut usize, shrink_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ShrinkError> {
        if shrink_to >= *cap {
            return Ok(());
        }
        if self.is_inline(*cap) {
            Ok(self.inline.shrink_capacity(cap, shrink_to, alloc)?)
        } else {
            if self.is_inline(shrink_to) {
                let (mut inline, new_cap) = InlineVecInnerWithoutCapacity::new();
                debug_assert!(new_cap >= shrink_to);
                core::ptr::copy_nonoverlapping(self.allocated.as_uninit_slice(*cap).as_ptr(), inline.as_uninit_slice_mut(new_cap).as_mut_ptr(), shrink_to);
                // this would only panic if T is zero-sized, but in that case then is_inline always returns true
                self.allocated.shrink_capacity(cap, 0, alloc).unwrap_unchecked();
                *cap = new_cap;
                self.inline = ManuallyDrop::new(inline);
                Ok(())
            } else {
                Ok(self.allocated.shrink_capacity(cap, shrink_to, alloc)?)
            }
        }
    }

    unsafe fn as_uninit_slice<'a>(&'a self, cap: usize) -> &'a [MaybeUninit<Self::Item>] {
        if self.is_inline(cap) {
            self.inline.as_uninit_slice(cap)
        } else {
            self.allocated.as_uninit_slice(cap)
        }
    }

    unsafe fn as_uninit_slice_mut<'a>(&'a mut self, cap: usize) -> &'a mut [MaybeUninit<Self::Item>] {
        if self.is_inline(cap) {
            self.inline.as_uninit_slice_mut(cap)
        } else {
            self.allocated.as_uninit_slice_mut(cap)
        }
    }

    unsafe fn dealloc(self, cap: usize, alloc: &Self::Allocator) {
        if self.is_inline(cap) {
            ManuallyDrop::into_inner(self.inline).dealloc(cap, alloc);
        } else {
            ManuallyDrop::into_inner(self.allocated).dealloc(cap, alloc);
        }
    }
}

impl <T, A: Allocator, const IN_CAP: usize> SmallVecInnerWithoutCapacity<T, A, IN_CAP> {
    fn is_inline(&self, cap: usize) -> bool {
        !self.is_allocated(cap)
    }

    fn is_allocated(&self, cap: usize) -> bool {
        size_of::<T>() > 0 && cap > IN_CAP
    }
}

/// **Internal use, changes will not constitute a breaking change.**
#[doc(hidden)]
pub struct InlineVecInnerWithoutCapacity<T, A: Allocator, const CAP: usize>([MaybeUninit<T>; CAP], PhantomData<A>);

impl <T, A: Allocator, const CAP: usize> VecInnerWithoutCapacity for InlineVecInnerWithoutCapacity<T, A, CAP> {
    type Item = T;

    type Allocator = A;

    type ReserveError = FixedSizeError;

    type ShrinkError = FixedSizeError;

    type Capacity = ();

    fn new() -> (Self, usize) {
        unsafe {
            let s = Self(MaybeUninit::uninit().assume_init(), PhantomData);
            if size_of::<T>() == 0 {
                // SAFETY: assuming init on an array of data that is known to be uninit
                (s, usize::MAX)
            } else {
                (s, CAP)
            }
        }
    }

    unsafe fn grow_capacity(&mut self, cap: &mut usize, grow_to: usize, _alloc: &Self::Allocator) -> Result<(), Self::ReserveError> {
        self.check_cap(*cap);
        if *cap == grow_to {
            Ok(())
        } else {
            Err(FixedSizeError::FixedSizeError)
        }
    }

    unsafe fn shrink_capacity(&mut self, cap: &mut usize, shrink_to: usize, _alloc: &Self::Allocator) -> Result<(), Self::ShrinkError> {
        self.check_cap(*cap);
        if shrink_to >= *cap {
            return Ok(());
        } else {
            Err(FixedSizeError::FixedSizeError)
        }
    }

    unsafe fn as_uninit_slice<'a>(&'a self, cap: usize) -> &'a [MaybeUninit<Self::Item>] {
        self.check_cap(cap);
        &self.0
    }

    unsafe fn as_uninit_slice_mut<'a>(&'a mut self, cap: usize) -> &'a mut [MaybeUninit<Self::Item>] {
        self.check_cap(cap);
        &mut self.0
    }
    
    unsafe fn dealloc(self, cap: usize, _alloc: &Self::Allocator) {
        self.check_cap(cap);
    }
}

impl <T, A: Allocator, const CAP: usize> InlineVecInnerWithoutCapacity<T, A, CAP> {
    #[mutants::skip("this function is the test, and I assert it is correct")]
    #[inline(always)]
    fn check_cap(&self, cap: usize) {
        #[cfg(debug_assertions)]
        if size_of::<T>() == 0 {
            assert_eq!(cap, usize::MAX);
        } else {
            assert_eq!(cap, CAP);
        }
    }
}

/// **Internal use, changes will not constitute a breaking change.**
#[doc(hidden)]
pub struct AllocatingVecInnerWithoutCapacity<T, A: Allocator>(NonNull<MaybeUninit<T>>, PhantomData<A>);

impl <T, A: Allocator> VecInnerWithoutCapacity for AllocatingVecInnerWithoutCapacity<T, A> {
    type Item = T;

    type Allocator = A;

    type ReserveError = AllocLayoutError;

    type ShrinkError = AllocError;

    type Capacity = usize;

    fn new() -> (Self, usize) {
        let s = Self(NonNull::dangling(), PhantomData);
        if size_of::<T>() == 0 {
            (s, usize::MAX)
        } else {
            (s, 0)
        }
    }

    unsafe fn grow_capacity(&mut self, cap: &mut usize, grow_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ReserveError> {
        if *cap >= grow_to {
            return Ok(());
        }
        if size_of::<T>() == 0 {
            debug_assert_eq!(*cap, usize::MAX);
            return Err(alloc::AllocError.into())
        }
        let new_ptr = if *cap == 0 {
            let layout = Layout::array::<MaybeUninit<T>>(grow_to)?;
            alloc.allocate(layout)?
        } else {
            let old_layout = Layout::array::<MaybeUninit<T>>(*cap)?;
            let new_layout = Layout::array::<MaybeUninit<T>>(grow_to)?;
            alloc.grow(self.0.cast(), old_layout, new_layout)?
        };
        *cap = new_ptr.len() / size_of::<T>();
        self.0 = new_ptr.cast();
        Ok(())
    }

    unsafe fn shrink_capacity(&mut self, cap: &mut usize, shrink_to: usize, alloc: &Self::Allocator) -> Result<(), Self::ShrinkError> {
        if shrink_to >= *cap {
            return Ok(());
        }
        if size_of::<T>() == 0 {
            return Err(AllocError::AllocError(alloc::AllocError))
        }
        // SAFETY: caller upholds that this `cap` was from a previously successful operation, which means an array layout was already constructed and checked with this size.
        let old_layout = Layout::array::<MaybeUninit<T>>(*cap).unwrap_unchecked();
        if shrink_to == 0 {
            alloc.deallocate(self.0.cast(), old_layout);
            *cap = 0;
        } else {
            // SAFETY: `shrink_to` must be smaller than `cap` by this point, which implies that the above always succeeding means this does too.
            let new_layout = Layout::array::<MaybeUninit<T>>(shrink_to).unwrap_unchecked();
            let new_ptr = alloc.shrink(self.0.cast(), old_layout, new_layout)?;
            *cap = new_ptr.len() / size_of::<T>();
            self.0 = new_ptr.cast();
        }
        Ok(())
    }

    unsafe fn as_uninit_slice<'a>(&'a self, cap: usize) -> &'a [MaybeUninit<Self::Item>] {
        NonNull::slice_from_raw_parts(self.0, cap).as_ref()
    }

    unsafe fn as_uninit_slice_mut<'a>(&'a mut self, cap: usize) -> &'a mut [MaybeUninit<Self::Item>] {
        NonNull::slice_from_raw_parts(self.0, cap).as_mut()
    }
    
    unsafe fn dealloc(self, cap: usize, alloc: &Self::Allocator) {
        if cap != 0 {
            // SAFETY: caller upholds that this `cap` was from a previously successful operation, which means an array layout was already constructed and checked with this size.
            let layout = Layout::array::<MaybeUninit<T>>(cap).unwrap_unchecked();
            alloc.deallocate(self.0.cast(), layout);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{alloc::{Allocator, Global}, list::vec_inner::{AllocatingVecInnerWithoutCapacity, InlineVecInnerWithoutCapacity, SmallVecInnerWithoutCapacity, VecInnerWithoutCapacity}};

    fn vec_inner_without_capacity_simple_loops<V: VecInnerWithoutCapacity>(alloc: &V::Allocator) {
        let (mut vec, mut cap) = V::new();
        if size_of::<V::Item>() == 0 {
            assert_eq!(cap, usize::MAX);
        }
        
        unsafe {
            for i in 0..100 {
                let old_cap = cap;
                let res = vec.grow_capacity(&mut cap, i, alloc);
                match res {
                    Ok(_) => assert!(old_cap <= cap),
                    Err(_) => assert_eq!(old_cap, cap),
                }
                if size_of::<V::Item>() == 0 {
                    assert_eq!(cap, usize::MAX);
                }
            }
            let old_cap = cap;
            let res = vec.shrink_capacity(&mut cap, 0, alloc);
            match res {
                Ok(_) => assert!(old_cap >= cap),
                Err(_) => assert_eq!(old_cap, cap),
            }
            if size_of::<V::Item>() == 0 {
                assert_eq!(cap, usize::MAX);
            }
            vec.dealloc(cap, alloc);
        }
    }

    #[test]
    fn small_vec_inner_without_capacity_simple() {
        let (mut vec, mut cap) = SmallVecInnerWithoutCapacity::<u8, _, 2>::new();
        unsafe {
            assert_eq!(cap, 2);
            assert!(vec.is_inline(cap));
            vec.grow_capacity(&mut cap, 4, &Global).unwrap();
            assert_eq!(cap, 4);
            assert!(vec.is_allocated(cap));
            vec.grow_capacity(&mut cap, 5, &Global).unwrap();
            assert_eq!(cap, 5);
            assert!(vec.is_allocated(cap));
            vec.shrink_capacity(&mut cap, 3, &Global).unwrap();
            assert_eq!(cap, 3);
            assert!(vec.is_allocated(cap));
            vec.shrink_capacity(&mut cap, 2, &Global).unwrap();
            assert_eq!(cap, 2);
            assert!(vec.is_inline(cap));
            vec.shrink_capacity(&mut cap, 0, &Global).unwrap_err();
            assert_eq!(cap, 2);
            assert!(vec.is_inline(cap));
            vec.dealloc(cap, &Global);
        }
    }

    #[test]
    fn small_vec_inner_without_capacity() {
        fn instance_test<T, A: Allocator, const IN_CAP: usize>(alloc: &A) {
            vec_inner_without_capacity_simple_loops::<SmallVecInnerWithoutCapacity<T, A, IN_CAP>>(alloc);
            if size_of::<T>() == 0 {
                return;
            }
            let (mut vec, mut cap) = SmallVecInnerWithoutCapacity::<T, A, IN_CAP>::new();
            assert_eq!(cap, IN_CAP);
            unsafe {
                vec.grow_capacity(&mut cap, IN_CAP + 1, &alloc).unwrap();
                assert_eq!(cap, IN_CAP + 1);
                vec.dealloc(cap, &alloc);
            }
        }

        fn multi_type<A: Allocator, const IN_CAP: usize>(alloc: &A) {
            instance_test::<(), A, IN_CAP>(alloc);
            instance_test::<u8, A, IN_CAP>(alloc);
            instance_test::<u32, A, IN_CAP>(alloc);
            instance_test::<[bool; 2], A, IN_CAP>(alloc);
        }

        fn multi_cap<A: Allocator>(alloc: &A) {
            multi_type::<A, 0>(alloc);
            multi_type::<A, 1>(alloc);
            multi_type::<A, 2>(alloc);
            multi_type::<A, 5>(alloc);
            multi_type::<A, 10>(alloc);
            multi_type::<A, 20>(alloc);
        }

        multi_cap(&Global);
    }

    #[test]
    fn inline_vec_inner_without_capacity() {
        fn instance_test<T, A: Allocator, const CAP: usize>(alloc: &A) {
            vec_inner_without_capacity_simple_loops::<InlineVecInnerWithoutCapacity<T, A, CAP>>(alloc);
            if size_of::<T>() == 0 {
                return;
            }
            let (mut vec, mut cap) = InlineVecInnerWithoutCapacity::<T, A, CAP>::new();
            assert_eq!(cap, CAP);
            unsafe {
                vec.grow_capacity(&mut cap, CAP + 1, &alloc).unwrap_err();
                assert_eq!(cap, CAP);
                let res = vec.shrink_capacity(&mut cap, 0, &alloc);
                if CAP == 0 {
                    assert!(res.is_ok());
                } else {
                    assert!(res.is_err());
                }
                vec.dealloc(cap, &alloc);
            }
            vec_inner_without_capacity_simple_loops::<InlineVecInnerWithoutCapacity<T, A, CAP>>(alloc);
        }

        fn multi_type<A: Allocator, const CAP: usize>(alloc: &A) {
            instance_test::<(), A, CAP>(alloc);
            instance_test::<u8, A, CAP>(alloc);
            instance_test::<u32, A, CAP>(alloc);
            instance_test::<[bool; 2], A, CAP>(alloc);
        }

        fn multi_cap<A: Allocator>(alloc: &A) {
            multi_type::<A, 0>(alloc);
            multi_type::<A, 1>(alloc);
            multi_type::<A, 2>(alloc);
            multi_type::<A, 5>(alloc);
            multi_type::<A, 10>(alloc);
            multi_type::<A, 20>(alloc);
        }

        multi_cap(&Global);
    }

    #[test]
    fn allocating_vec_inner_without_capacity() {
        vec_inner_without_capacity_simple_loops::<AllocatingVecInnerWithoutCapacity<(), Global>>(&Global);
        vec_inner_without_capacity_simple_loops::<AllocatingVecInnerWithoutCapacity<u8, Global>>(&Global);
        vec_inner_without_capacity_simple_loops::<AllocatingVecInnerWithoutCapacity<u32, Global>>(&Global);
        vec_inner_without_capacity_simple_loops::<AllocatingVecInnerWithoutCapacity<[bool; 2], Global>>(&Global);

        let (mut vec, mut cap) = AllocatingVecInnerWithoutCapacity::<u8, Global>::new();
        assert_eq!(cap, 0);
        unsafe {
            vec.grow_capacity(&mut cap, 1, &Global).unwrap();
            assert_eq!(cap, 1);
            vec.grow_capacity(&mut cap, 1, &Global).unwrap();
            assert_eq!(cap, 1);
            vec.grow_capacity(&mut cap, 2, &Global).unwrap();
            assert_eq!(cap, 2);
            vec.shrink_capacity(&mut cap, 0, &Global).unwrap();
            assert_eq!(cap, 0);
        }
    }
}
