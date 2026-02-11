#![feature(const_trait_impl)]
#![feature(const_try)]
#![feature(const_default)]

use bitfields::bitfield;

#[bitfield(u16)]
pub struct Bitfield {
    a: u8,
    a: u8,
}

fn main() {}
