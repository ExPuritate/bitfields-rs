#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield(u32)]
pub struct Bitfield {
    #[bits(default = 0x12, access = wo)]
    a: u32,
}

fn main() {
    let bitfield = BitfieldBuilder::new();
    bitfield.a(); // Error, field is write-only
}
