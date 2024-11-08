use std::{ io, fs, path::PathBuf, };
use log::{ info, warn };
use xmas_elf::ElfFile;

use thiserror::Error;



///
/// Errors which may occur when loading `InputData`.
///
#[derive(Error, Debug)]
pub enum InputError
{
        #[error("std::fs::read() raised this error: {0:?}")]
        IoErr(#[from] io::Error),

        #[error("Not a valid ELF.")]
        BadXmas(String),

        #[error("Section {0} was could not be found.")]
        CouldNotFindSection(String),
}



///
/// Containing the successfully loaded data.
///
#[derive(Clone, Debug)]
pub struct InputData
{
    pub elf_path:   PathBuf,
    pub elf_bytes:  Vec<u8>,
    pub bc_path:    PathBuf,
    pub bc_bytes:   Vec<u8>,
}


#[allow(clippy::new_without_default)] // default doesn't make sense
impl InputData
{
    pub fn new() -> Self {
        InputData
        {
            elf_path:  PathBuf::new(),
            elf_bytes: vec![],
            bc_path:   PathBuf::new(),
            bc_bytes:  vec![],
        }
    }
}

///
/// Load the file provided by `elf_fp`.
/// Then looks for the section `.llvmbc` (LLVM Bit Code) within the file.
/// If the section isn't found within the ELF, it instead adds "bc" to the
/// path and loads that file as the bit code segment.\
/// \
/// Given that `elf_fp` is `target/my_bin.elf` it will first read
/// `my_bin.elf`. If the section `.lvvmbc` is contained, then it's done.
/// If the section `.llvmbc` is not found it reads `my_bin.elfbc` and
/// treats that as the bitcode segment. No validity checks is dode if the
/// file `my_bin.elfbc` is used.
///
pub fn load_elf_and_potentially_bcfile(elf_fp: PathBuf)
    -> Result<InputData, InputError>
{
    let elf_path = elf_fp.clone();


    let elf_bytes: Vec<u8>  = fs::read(&elf_fp).map_err(|e|
                        InputError::IoErr(e))?;

    // Trying to create an ELF
    let elf = ElfFile::new(&elf_bytes).map_err(|s|
                InputError::BadXmas( s.to_string() ))?;

    if elf.find_section_by_name(".stack_sizes").is_none()
    {
        return Err( InputError::CouldNotFindSection(".stack_sizes".to_string()) );
    }

    // LLVM Bit Code section header; first look in the ELF for it.
    if let Some(bc_sec_hdr) = elf.find_section_by_name(".llvmbc")
    {
        
        let bc_path = elf_path.clone();
        info!("ELF with .llvmbc section found.");
        let bc_bytes = bc_sec_hdr.raw_data(&elf).to_vec();

        let inp = InputData
        {
            elf_path,
            elf_bytes,
            bc_path,
            bc_bytes,
        };
        Ok(inp)
    }
    else
    {
        // No LLVMBC section found, look elsewhere
        let bc_path = elf_path.clone().with_extension("bc");
        warn!("No .llvmbc in ELF,  looking for bc file {:?}", bc_path);

        let bc_bytes = fs::read(&bc_path)?;

        let inp = InputData
        {
            elf_path,
            elf_bytes,
            bc_path,
            bc_bytes,
        };
        Ok(inp)
    }
}



