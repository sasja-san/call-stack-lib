use std::ffi::CStr;
use std::ptr::null_mut;
use std::str;

// use anyhow::bail;
use llvm_sys::core::*;
use llvm_sys::prelude::{LLVMBasicBlockRef, LLVMModuleRef, LLVMTypeRef, LLVMValueRef};

#[derive(Clone, Debug)]
pub struct Module {
    pub declares: Vec<DeclaredFunction>,
    pub defines: Vec<Function>,
}

#[derive(Clone, Debug)]
pub struct DeclaredFunction {
    pub name: String,
    pub sig: String,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub sig: String,
    pub callees: Vec<Callee>,
}

#[derive(Clone, Debug)]
pub enum Callee {
    Direct(DirectCallee),
    Indirect(IndirectCallee),
}

#[derive(Clone, Debug)]
pub struct DirectCallee {
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct IndirectCallee {
    pub sig: String,
}

pub fn parse(bitcode: &[u8]) -> Result<Module, &str> {
    unsafe {
        let lcx = LLVMContextCreate();

        let len = bitcode.len();
        let buf = LLVMCreateMemoryBufferWithMemoryRange(bitcode.as_ptr() as _, len, null_mut(), 0);

        let mut module = null_mut();
        let return_code = llvm_sys::bit_reader::LLVMParseBitcodeInContext2(lcx, buf, &mut module);
        LLVMDisposeMemoryBuffer(buf);
        if return_code != 0 {
            return Err("Failed to parse bitcode")
        }

        let mut res = Module {
            declares: Vec::new(),
            defines: Vec::new(),
        };

        for f in iter_funcs(module) {
            if LLVMIsDeclaration(f) != 0 {
                continue;
            }

            let mut ff = Function {
                name: value_name(f),
                sig: stringify_ty(LLVMGlobalGetValueType(f)),
                callees: Vec::new(),
            };

            for bb in iter_basic_blocks(f) {
                for inst in iter_instructions(bb) {
                    if LLVMIsACallInst(inst).is_null() {
                        continue;
                    }

                    let callee = LLVMGetCalledValue(inst);
                    if !LLVMIsAInlineAsm(callee).is_null() {
                        //println!("inline asm");
                    } else if !LLVMIsAConstant(callee).is_null() {
                        // direct call
                        let name = value_name(callee);
                        if !name.starts_with("llvm.") {
                            ff.callees.push(Callee::Direct(DirectCallee { name }))
                        }
                    } else {
                        // indirect call
                        let ty = stringify_ty(LLVMGetCalledFunctionType(inst));
                        ff.callees
                            .push(Callee::Indirect(IndirectCallee { sig: ty }))
                    }
                }
            }

            res.defines.push(ff);
        }

        Ok(res)
    }
}

unsafe fn stringify(v: LLVMValueRef) -> String {
    CStr::from_ptr(LLVMPrintValueToString(v))
        .to_str()
        .unwrap()
        .to_owned()
}
unsafe fn stringify_ty(v: LLVMTypeRef) -> String {
    CStr::from_ptr(LLVMPrintTypeToString(v))
        .to_str()
        .unwrap()
        .to_owned()
}

unsafe fn value_name(v: LLVMValueRef) -> String {
    let mut len = 0;
    let mut _p = LLVMGetValueName2(v, &mut len); // surpress mut warning
    str::from_utf8_unchecked(std::slice::from_raw_parts(_p as _, len)).to_owned()
}

unsafe fn iter_funcs(m: LLVMModuleRef) -> impl Iterator<Item = LLVMValueRef> {
    let mut f = LLVMGetFirstFunction(m);
    std::iter::from_fn(move || {
        if f.is_null() {
            None
        } else {
            let f2 = f;
            f = LLVMGetNextFunction(f2);
            Some(f2)
        }
    })
}

unsafe fn iter_basic_blocks(m: LLVMValueRef) -> impl Iterator<Item = LLVMBasicBlockRef> {
    let mut f = LLVMGetFirstBasicBlock(m);
    std::iter::from_fn(move || {
        if f.is_null() {
            None
        } else {
            let f2 = f;
            f = LLVMGetNextBasicBlock(f2);
            Some(f2)
        }
    })
}

unsafe fn iter_instructions(m: LLVMBasicBlockRef) -> impl Iterator<Item = LLVMValueRef> {
    let mut f = LLVMGetFirstInstruction(m);
    std::iter::from_fn(move || {
        if f.is_null() {
            None
        } else {
            let f2 = f;
            f = LLVMGetNextInstruction(f2);
            Some(f2)
        }
    })
}

