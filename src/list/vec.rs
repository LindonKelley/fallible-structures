use core::marker::PhantomData;

use crate::alloc::Allocator;

struct Vec<T, A: Allocator> {
    __phantom: PhantomData<(T, A)>
}
