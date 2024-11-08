use log::warn;

use std::ffi::CStr;
use std::ptr::null_mut;
use std::str;

use llvm_sys::core::*;
use llvm_sys::prelude::{LLVMBasicBlockRef, LLVMModuleRef, LLVMTypeRef, LLVMValueRef};

use petgraph::graph::NodeIndex;
use std::collections::HashSet;

use crate as c;
use crate::state::State;


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

/*     ██████╗  █████╗ ██████╗ ███████╗███████╗     */
/*     ██╔══██╗██╔══██╗██╔══██╗██╔════╝██╔════╝     */
/*     ██████╔╝███████║██████╔╝███████╗█████╗       */
/*     ██╔═══╝ ██╔══██║██╔══██╗╚════██║██╔══╝       */
/*     ██║     ██║  ██║██║  ██║███████║███████╗     */
/*     ╚═╝     ╚═╝  ╚═╝╚═╝  ╚═╝╚══════╝╚══════╝     */

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

#[allow(dead_code)]
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


















/*      ███████╗████████╗ █████╗ ████████╗███████╗       */
/*      ██╔════╝╚══██╔══╝██╔══██╗╚══██╔══╝██╔════╝       */
/*      ███████╗   ██║   ███████║   ██║   █████╗         */
/*      ╚════██║   ██║   ██╔══██║   ██║   ██╔══╝         */
/*      ███████║   ██║   ██║  ██║   ██║   ███████╗       */
/*      ╚══════╝   ╚═╝   ╚═╝  ╚═╝   ╚═╝   ╚══════╝       */
/*     ███████████████████████████████████████████╗      */
/*     ╚══════════════════════════════════════════╝      */

impl State
{

    /// 
    /// Modified fields:
    /// - `defined`
    /// - `edges`
    /// - `g`
    /// - `llvm_seen`
    /// - `indices`
    /// - `indirects`
    ///
    pub fn process_llvm_bitcode(&mut self)
    {
        for define in self.defines.values()
        {
            let canonical_name = match self.aliases.get(define.name.as_str())
            {
                Some(canonical_name) => canonical_name,
                None                 => { continue; } // symbol GC-ed by linker, skip
            };
            self.defined.insert(canonical_name.to_string());
            let caller: NodeIndex = self.indices[canonical_name];
            let callees_seen: &mut HashSet<NodeIndex> = self.edges.entry(caller).or_default();

            for stmt in &define.callees
            {
                match stmt
                {
                    /*
                    Stmt::Asm(expr) => {
                        if fns_containing_asm.insert(*canonical_name) {
                            // NB: we only print the first inline asm statement in a function
                            warn!(
                                "assuming that asm!(\"{}\") does *not* use the stack in `{}`",
                                expr, canonical_name
                            );
                        }
                    }
                    // this is basically `(mem::transmute<*const u8, fn()>(&__some_symbol))()`
                    Stmt::BitcastCall(sym) => {
                        // XXX we have some type information for this call but it's unclear if we should
                        // try harder -- does this ever occur in pure Rust programs?

                        let sym = sym.expect("BUG? unnamed symbol is being invoked");
                        let callee = if let Some(idx) = indices.get(sym) {
                            *idx
                        } else {
                            warn!("no stack information for `{}`", sym);

                            let idx = g.add_node(Node(sym, None, false));
                            indices.insert(Cow::Borrowed(sym), idx);
                            idx
                        };

                        g.add_edge(caller, callee, ());
                    }
                    */

                    Callee::Direct(callee) =>
                    {
                        let func = callee.name.as_str();
                        match func
                        {
                            // no-op / debug-info
                            "llvm.dbg.value"    => continue,
                            "llvm.dbg.declare"  => continue,

                            // no-op / compiler-hint
                            "llvm.assume"       => continue,

                            // lowers to a single instruction
                            "llvm.trap"         => continue,

                            _                   => {}
                        }

                        // no-op / compiler-hint
                        if func.starts_with("llvm.lifetime.start")
                            || func.starts_with("llvm.lifetime.end")
                        {
                            continue;
                        }

                        let mut call = |callee| 
                        {
                            if !callees_seen.contains(&callee) {
                                self.g.add_edge(caller, callee, ());
                                callees_seen.insert(callee);
                            }
                        };

                        if self.target.is_thumb() && func.starts_with("llvm.")
                        {
                            // we'll analyze the machine code in the ELF file to 
                            // figure out what these lower to
                            continue;
                        }

                        // TODO? consider alignment and `value` argument to only include one edge
                        // TODO? consider the `len` argument to elide the call to `*mem*`
                        if func.starts_with("llvm.memcpy.")
                        {
                            if let Some(callee) = self.indices.get("memcpy")            { call(*callee); }
                            // ARMv7-R and the like use these
                            if let Some(callee) = self.indices.get("__aeabi_memcpy")    { call(*callee); }
                            if let Some(callee) = self.indices.get("__aeabi_memcpy4")   { call(*callee); }

                            continue;
                        }

                        // TODO? consider alignment and `value` argument to only include one edge
                        // TODO? consider the `len` argument to elide the call to `*mem*`
                        if func.starts_with("llvm.memset.") || func.starts_with("llvm.memmove.")
                        {
                            if let Some(callee) = self.indices.get("memset")            { call(*callee); }
                            // ARMv7-R and the like use these
                            if let Some(callee) = self.indices.get("__aeabi_memset")    { call(*callee); }
                            if let Some(callee) = self.indices.get("__aeabi_memset4")   { call(*callee); }
                            if let Some(callee) = self.indices.get("memclr")            { call(*callee); }
                            if let Some(callee) = self.indices.get("__aeabi_memclr")    { call(*callee); }
                            if let Some(callee) = self.indices.get("__aeabi_memclr4")   { call(*callee); }

                            continue;
                        }

                        // XXX unclear whether these produce library calls on some platforms or not
                        if func.starts_with("llvm.abs.")
                            || func.starts_with("llvm.bswap.")
                            || func.starts_with("llvm.ctlz.")
                            || func.starts_with("llvm.cttz.")
                            || func.starts_with("llvm.sadd.with.overflow.")
                            || func.starts_with("llvm.smul.with.overflow.")
                            || func.starts_with("llvm.ssub.with.overflow.")
                            || func.starts_with("llvm.uadd.sat.")
                            || func.starts_with("llvm.uadd.with.overflow.")
                            || func.starts_with("llvm.umax.")
                            || func.starts_with("llvm.umin.")
                            || func.starts_with("llvm.umul.with.overflow.")
                            || func.starts_with("llvm.usub.sat.")
                            || func.starts_with("llvm.usub.with.overflow.")
                            || func.starts_with("llvm.vector.reduce.")
                            || func.starts_with("llvm.x86.sse2.pmovmskb.")
                            || func == "llvm.x86.sse2.pause"
                        {
                            if !self.llvm_seen.contains(func)
                            {
                                self.llvm_seen.insert(func.to_string());
                                warn!("assuming that `{}` directly lowers to machine code", func);
                            }

                            continue;
                        }

                        // noalias metadata does not lower to machine code
                        if func == "llvm.experimental.noalias.scope.decl"
                        {
                            continue;
                        }

                        assert!(
                            !func.starts_with("llvm."),
                            "BUG: unhandled llvm intrinsic: {}",
                            func
                        );

                        // some intrinsics can be directly lowered to machine code
                        // if the intrinsic has no corresponding node (symbol in the output ELF) assume
                        // that it has been lowered to machine code
                        const SYMBOLLESS_INTRINSICS: &[&str] = &["memcmp"];
                        if SYMBOLLESS_INTRINSICS.contains(&func) && !self.indices.contains_key(func) {
                            continue;
                        }

                        // use canonical name
                        let callee = if let Some(canon) = self.aliases.get(func)
                        {
                            self.indices[canon]
                        }
                        else if self.symbols.undefined.contains(func)
                        {
                            // ESP32 variants use functions that are located
                            // in the ROM and are missing from firmware ELFs. 
                            // Let's try to work with those SoCs, too.
                            // - bugadani
                            //
                            // (changed assert!() to warn!())
                            warn!("callee `{}` is unknown", func);
                            continue;
                        }
                        else
                        {
                            if let Some(idx) = self.indices.get(func) 
                            {
                                *idx
                            }
                            else
                            {
                                let idx = self.g.add_node(c::Node(func.to_string(), None, false));
                                self.indices.insert((*func).into(), idx);

                                idx
                            }
                        };

                        if !callees_seen.contains(&callee) 
                        {
                            callees_seen.insert(callee);
                            self.g.add_edge(caller, callee, ());
                        }
                    }
                    Callee::Indirect(callee) => {
                        for (key_sig, indirect) in &mut self.indirects 
                        {
                            if *key_sig == callee.sig 
                            {
                                indirect.called = true;
                                indirect.callers.insert(caller);
                            }
                        }
                    }
                }
            }
        }
    }

}

