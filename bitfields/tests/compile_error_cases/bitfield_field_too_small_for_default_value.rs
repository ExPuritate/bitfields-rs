#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield(u16)]
pub struct Bitfield {
    #[bits(default = 0xFFFF)]
    a: u8,
    #[bits(default = 1)]
    b: u8,
}

fn main() {}
