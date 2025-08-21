use error_set::error_set;
use crate::alloc;

error_set! {
    AllocLayoutError = AllocError || LayoutError;

    FixedSizeAllocError = AllocError || FixedSizeError;

    AllocError = { AllocError(alloc::AllocError) };

    LayoutError = { LayoutError(alloc::LayoutError) };

    FixedSizeError = { FixedSizeError };
}
