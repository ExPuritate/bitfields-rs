#![feature(const_trait_impl)]
#![feature(const_try)]
#![feature(const_default)]

use bitfields::bitfield;

#[bitfield(u8)]
struct Bitfield {
    #[bits(access = ro)]
    _padding: u8,
}

fn main() {}
