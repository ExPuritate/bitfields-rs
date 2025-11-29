#![feature(const_trait_impl)]
#![feature(const_try)]

use bitfields::bitfield;

#[bitfield]
pub enum NonStruct {
    A = 1,
}

fn main() {}
