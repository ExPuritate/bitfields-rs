#![feature(const_trait_impl)]
#![feature(const_try)]
#![feature(const_default)]

use bitfields::bitfield;

#[bitfield(u32)]
pub struct Bitfield {
    a: u8,
    b: u8,
    c: u8,
    d: u16,
}

fn main() {}
