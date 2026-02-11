#![cfg_attr(not(feature = "std"), no_std)]
#![feature(const_trait_impl)]
#![feature(thread_id_value)]

pub use bitfields_impl::bitfield;

pub const trait IntoBits {
    type Number: Clone + Copy;
    fn into_bits(self) -> Self::Number;
}

pub const trait FromBits {
    type Number: Clone + Copy;
    fn from_bits(bits: Self::Number) -> Self;
}

#[cfg(feature = "std")]
mod std_impl;
