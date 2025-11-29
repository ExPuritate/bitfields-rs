#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield(u8)]
struct Bitfield {
    #[bits(access = ro)]
    _padding: u8,
}

fn main() {}
