#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield(i32)]
pub struct Bitfield {
    a: u8,
    b: u8,
    c: u8,
}

fn main() {}
