use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::{self,File},
    io::{self, stderr, Error, Write}, 
    path::PathBuf, 
    str::FromStr
};

/**
* Reference implementation, using call_stack_lib.
* Anyone using this library should probably keep 
* the exact function call order that's shown here.
*
* The file `dice` is a binary which was a university
* course lab. It's for an STM32 Nucleo. It's some
* HAL usage, turning on/off 13 LEDs and reading the
* button on the board. Nothing too complicated but 
* nothing trivial either.
*/

use call_stack_lib as cs;

const EXAMPLE_ELF: &str = "examples/dice";
const DOT_OUTPUT : &str = "dice.dot";


fn main()
{
    let p        = PathBuf::from_str(EXAMPLE_ELF).unwrap();
    let inp_load = cs::input::load_elf_and_potentially_bcfile(p);
    match &inp_load
    {
        Ok(inp) => println!("ELF/BC load OK"),
        Err(e)  => 
        {
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

    let mut s = cs::state::State::empty();

    // impl in state.rs
    s.load_input(inp, target);
    s.clear_thumb_bit();
    s.indexing_from_stack_sizes_section();
    s.remove_version_strings_from_undefined_symbols();
    s.default_method_demangle_pass();
    s.add_real_nodes();
    
    // impl in ir.rs
    s.process_llvm_bitcode();

    // impl in thumb.rs
    s.process_elf_machine_code();

    // impl in state.rs
    s.warn_for_unmodified_bits();
    s.add_indirect_calls_to_graph();
    s.filter_call_graph(None); // arg is `starting_node`
    s.stack_usage_analysis();
    s.unambiguously_shorten_symbol_names();

    // impl in output/top.rs
    {   // print TOP to stdout
        let stdout = std::io::stdout().lock();
        s.output_top(stdout);
    } 

    // impl in output/dot.rs
    {   // print DOT to file
        let fout = File::create(DOT_OUTPUT);
        let conf = cs::output::DotConf::default();
        let _ = match &fout
        {
            Ok(fh) => s.output_dot(fh, conf),
            Err(e) => writeln!(stderr(), "{:?}", e),
        };
    } 
}

