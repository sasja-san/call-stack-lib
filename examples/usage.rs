#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(clippy::redundant_field_names)]


use call_stack_lib as cs;


const EXAMPLE_ELF: &str = "examples/dice";


use std::{
    io::{self,Error},
    fs::{self,File},
    str::FromStr,
    path::PathBuf,


    collections::{BTreeMap, HashMap, HashSet},
};

use stack_sizes;

fn main()
{
    let p = PathBuf::from_str(EXAMPLE_ELF).unwrap();
    let inp_load = cs::inp::load_elf_and_potentially_bcfile(p);
    match &inp_load
    {
        Ok(inp) => println!("ELF/BC load OK"),
        Err(e)  => {
            println!("Error loading ELF/BC!"); 
            println!("{:?}",e);
            std::process::exit(1);
        },
    }

    let inp = inp_load.unwrap();

    // The target string will probably be a command line argument,
    // or perhaps parsed from the cargo files in the target project.
    let target = cs::Target::from_str("thumbv7m-none-eabi");
    println!("Target is {:?}", &target);

    let mut s = cs::State::empty();
    s.load_input(inp, target);


}
