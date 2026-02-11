#![feature(const_trait_impl)]
#![feature(const_try)]
#![feature(const_default)]

use bitfields::bitfield;

#[bitfield]
pub enum NonStruct {
    A = 1,
}

fn main() {}
