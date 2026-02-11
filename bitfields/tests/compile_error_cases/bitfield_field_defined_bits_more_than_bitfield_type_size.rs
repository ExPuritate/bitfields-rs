#![feature(const_trait_impl)]
#![feature(const_try)]
#![feature(const_default)]

use bitfields::bitfield;

#[bitfield(u32)]
pub struct Bitfield {
    #[bits(8)]
    a: u8,
    #[bits(7)]
    b: u8,
    #[bits(5)]
    c: u8,
    #[bits(16)]
    d: u16,
}

fn main() {}
