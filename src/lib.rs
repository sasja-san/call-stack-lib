
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(clippy::redundant_field_names)]

pub mod inp;
pub mod ir;
pub mod thumb;

mod prelude;
pub use prelude::*;

pub fn lib_print()
{
    println!("I am a visitor from the library. Gimme books!");
}


