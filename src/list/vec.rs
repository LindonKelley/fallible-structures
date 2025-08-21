use core::marker::PhantomData;

use crate::alloc::Allocator;

pub struct Vec<T, A: Allocator> {
    __phantom: PhantomData<(T, A)>
}
