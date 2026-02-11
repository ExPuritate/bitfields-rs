use core::num::NonZero;
use std::thread::ThreadId;

use crate::{FromBits, IntoBits};

impl const FromBits for ThreadId {
    type Number = u64;

    #[track_caller]
    fn from_bits(bits: Self::Number) -> Self {
        #[allow(unused)]
        struct Assert<const B: bool>;
        #[allow(unused)]
        trait True {}
        impl True for Assert<true> {}
        fn _assert()
        where
            Assert<
                {
                    (size_of::<ThreadId>() == size_of::<u64>())
                        && (align_of::<ThreadId>() == align_of::<u64>())
                },
            >: True,
        {
        }

        unsafe { std::mem::transmute(NonZero::new(bits).unwrap()) }
    }
}

impl const IntoBits for ThreadId {
    type Number = u64;

    fn into_bits(self) -> Self::Number {
        unsafe { std::mem::transmute(self) }
    }
}
