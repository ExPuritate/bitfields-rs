#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield(u32)]
struct Reg {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
}

fn main() {}
