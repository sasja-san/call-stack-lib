
/*      ███████╗████████╗ █████╗ ████████╗███████╗       */
/*      ██╔════╝╚══██╔══╝██╔══██╗╚══██╔══╝██╔════╝       */
/*      ███████╗   ██║   ███████║   ██║   █████╗         */
/*      ╚════██║   ██║   ██╔══██║   ██║   ██╔══╝         */
/*      ███████║   ██║   ██║  ██║   ██║   ███████╗       */
/*      ╚══════╝   ╚═╝   ╚═╝  ╚═╝   ╚═╝   ╚══════╝       */
/*     ███████████████████████████████████████████╗      */
/*     ╚══════════════════════════════════════════╝      */

use crate::thumb;
use crate::inp;
use crate::ir;
use crate as c; // call-stack-lib
use crate::Target;

use std::collections::{
    BTreeMap,
    HashMap, HashSet,
};
use stack_sizes as ss;
use petgraph::{
    algo,
    graph::{DiGraph, NodeIndex},
    visit::{Dfs, Reversed, Topo},
    Direction, Graph,
};
use xmas_elf::{
    sections::{SectionData, SectionHeader},
    symbol_table::Entry, 
    ElfFile
};

use log::{error, warn, info, trace};


#[derive(Clone, Debug)]
pub struct State
{
    pub input:                  crate::inp::InputData,
    pub target:                 Target,
    pub declares:               HashMap<String, ir::DeclaredFunction>,
    pub defines:                HashMap<String, ir::Function>,

    /// The result of the computation done through the
    /// `stack_sizes::analyze_executable()`
    pub symbols:                ss::Functions,
    pub stack_sizes:            HashMap<String, ss::Function>,

    pub g:                      Graph<c::Node, ()>,

    pub indices:                BTreeMap<String, NodeIndex>,
    pub indirects:              HashMap<String, c::Indirect>,

    
    pub aliases:                HashMap<String, String>,
    pub ambiguous:              HashMap<String, u32>,

    pub default_methods:        HashSet<String>,

    pub has_stack_usage_info:   bool,
    pub has_untyped_symbols:    bool,

    pub addr2name:              BTreeMap<u64, String>,

    pub fns_containing_asm:     HashSet<String>,
    pub llvm_seen:              HashSet<String>,

    // NodeIx -> [NodeIx]
    pub edges:                  HashMap<NodeIndex, HashSet<NodeIndex>>,
    pub defined:                HashSet<String>,

    pub cycles:                 Vec< Vec<NodeIndex> >,
}


/// This is ported from the code in `src/main.rs::run()` from
/// https://github.com/Dirbaio/cargo-call-stack (commit 
/// 49c395ea310a16896f1bcbf3f0377a125be5ab66).
///
/// Since it was all based on one giant function (820 lines) it was
/// hard to know where to draw the lines (outside of input/output).
impl State
{

    /// All variables initialized to empty/zero values.
    pub fn empty() -> Self
    {
        State
        {
            input:                  crate::inp::InputData::new(),
            target:                 Target::Other,
            declares:               HashMap::new(),
            defines:                HashMap::new(),
            symbols:                ss::Functions
            {
                have_32_bit_addresses:  false,
                undefined:              std::collections::HashSet::new(),
                defined:                std::collections::BTreeMap::new(),
            },
            stack_sizes:            HashMap::new(),
            g:                      DiGraph::new(),
            indices:                BTreeMap::new(),
            indirects:              HashMap::new(),
            aliases:                HashMap::new(),
            ambiguous:              HashMap::new(),
            default_methods:        HashSet::new(),
            has_stack_usage_info:   false,
            has_untyped_symbols:    false,
            addr2name:              BTreeMap::new(),
            fns_containing_asm:     HashSet::new(),
            llvm_seen:              HashSet::new(),
            edges:                  HashMap::new(),
            defined:                HashSet::new(),
            cycles:                 vec![],
        }
    }


    ///
    /// Modified symbols:
    ///     - `target`
    ///     - `input`
    ///     - `declares`
    ///     - `defines`
    ///     - `symbols`
    ///
    // NOTE: lines 100 - 118
    pub fn load_input(&mut self, inp_data: inp::InputData, target: Target)
    {
        self.target = target;
        // share the inp_data around a bit before transferring ownership
        let parsed_bitcode = ir::parse(&inp_data.bc_bytes).unwrap();

        // make tuples of (name, thingy)
        self.declares   = parsed_bitcode.declares
                                        .into_iter()
                                        .map(|d| (d.name.clone(), d))
                                        .collect();
        self.defines    = parsed_bitcode.defines
                                        .into_iter()
                                        .map(|d| (d.name.clone(), d))
                                        .collect();

        // extract stack size information
        // extract list of "live" symbols (symbols that have not been GC-ed by the linker)
        // this time we use the ELF and not the object file
        self.symbols = ss::analyze_executable(&inp_data.elf_bytes).unwrap();

        self.input  = inp_data;
    }

    /// Modified fields:
    /// - symbols
    // NOTE: lines 119 - 127
    pub fn clear_thumb_bit(&mut self)
    {
        // Clear the thumb bit.
        if self.target.is_thumb()
        {
            self.symbols.defined = self.symbols.defined
                .clone()
                .into_iter()
                .map(|(k, v)| (k & !1, v))
                .collect();
        }
    }


    /// Modified fields:
    /// - stack_sizes
    // NOTE: lines 128 - 135
    pub fn indexing_from_stack_sizes_section(&mut self)
    {
        for (_addr, func) in &self.symbols.defined
        {
            for name in &func.names
            {
                self.stack_sizes.insert(name.clone(), func.clone());
            }
        }
    }

    /// Modified fields:
    /// - symbols.undefined
    // NOTE: lines 136 - 148
    pub fn remove_version_strings_from_undefined_symbols(&mut self)
    {

        self.symbols.undefined = self.symbols
            .undefined
            .clone()
            .into_iter()
            .map(|sym|
                {
                    if let Some(name) = sym.rsplit("@@").nth(1)
                    {
                        name.to_string()
                    }
                    else
                    {
                        sym
                    }
                }
            )
            .collect();
    }

    // NOTE: lines 149 - 163 is var inits

    /// Modified fields:
    /// - default_methods
    // NOTE: lines 164 - 183
    pub fn default_method_demangle_pass(&mut self)
    {
        for name in self.defines.keys()
        {
            let demangled = rustc_demangle::demangle(name).to_string();

            // `<crate::module::Type as crate::module::Trait>::method::hdeadbeef`
            if demangled.starts_with("<")
            {
                if let Some(rhs) = demangled.splitn(2, " as ").nth(1)
                {
                    // rhs = `crate::module::Trait>::method::hdeadbeef`
                    let mut parts = rhs.splitn(2, ">::");

                    if let (Some(trait_), Some(rhs)) = (parts.next(), parts.next())
                    {
                        // trait_ = `crate::module::Trait`, rhs = `method::hdeadbeef`

                        if let Some(method) = dehash(rhs) {
                            self.default_methods.insert(format!("{}::{}", trait_, method));
                        }
                    }
                }
            }
        }
    }

    // NOTE: lines 184 - 187 is var inits

    /// Modified fields:
    /// - aliases
    /// - addr2name
    /// - has_stack_usage_info
    /// - ambiguous
    /// - indices
    /// - indirects
    /// - has_untyped_symbols
    // NOTE: lines 188 - 267
    pub fn add_real_nodes(&mut self)
    {
        let syms = self.symbols.clone();
        for (address, sym) in syms.defined {
            let names = sym.names;
            // filter out tags
            let names = names
                .iter()
                .filter_map(|name| {
                    if name == "$a"
                        || name.starts_with("$a.")
                        || name == "$x"
                        || name.starts_with("$x.")
                    {
                        None
                    } else {
                        Some(name)
                    }
                })
                .collect::<Vec<_>>();

            /*
            let canonical_name = if names.len() > 1 {
                // if one of the aliases appears in the `stack_sizes` dictionary, use that
                if let Some(needle) = names.iter().find(|name| stack_sizes.contains_key(&***name)) {
                    needle
                } else {
                    // otherwise, pick the first name that's not a tag
                    names[0]
                }
            } else {
                names[0]
            };
            */
            let canonical_name = names[0];

            for name in names.iter().cloned() {
                self.aliases.insert(name.to_string(), canonical_name.to_string());
            }

            let _out = self.addr2name.insert(address, canonical_name.to_string());
            debug_assert!(_out.is_none());

            let stack = self.stack_sizes
                .get(canonical_name)
                .cloned()
                .and_then(|s| s.stack);
            if stack.is_none()
            {
                if !self.target.is_thumb()
                {
                    warn!("no stack usage information for `{}`", canonical_name);
                }
            }
            else 
            {
                self.has_stack_usage_info = true;
            }

            let demangled = rustc_demangle::demangle(&canonical_name).to_string();
            if let Some(dehashed) = dehash(&demangled)
            {
                *self.ambiguous.entry(dehashed.to_string()).or_insert(0) += 1;
            }

            let idx = self.g.add_node(c::Node(canonical_name.clone(), stack, false));
            self.indices.insert(canonical_name.into(), idx);

            if let Some(def) = names
                    .iter()
                    .filter_map(|&name| self.defines.get(name))
                    .next()
            {
                self.indirects
                    .entry(def.sig.clone())
                    .or_default()
                    .callees
                    .insert(idx);
            }
            else if let Some(sig) = names
                    .iter()
                    .filter_map(|&name| 
                        self.declares.get(name)
                                .and_then(|decl| Some(decl.sig.clone())))
                    .next()
            {
                self.indirects.entry(sig).or_default().callees.insert(idx);
            }
            else if !is_outlined_function(&canonical_name)
            {
                // ^ functions produced by LLVM's function outliner are never called through function
                // pointers (as of LLVM 14.0.6)
                self.has_untyped_symbols = true;
                warn!("no type information for `{}`", canonical_name);
            }
        }

    }

    // NOTE: lines 268 - 273 is var inits




    // Modified fields:
    // - 
    // NOTE: lines 486 - 681
    pub fn process_elf_machine_code(&mut self)
    {
        // here we parse the machine code in the ELF file to find out edges that don't appear in the
        // LLVM-IR (e.g. `fadd` operation, `call llvm.umul.with.overflow`, etc.) or are difficult to
        // disambiguate from the LLVM-IR (e.g. does this `llvm.memcpy` lower to a call to
        // `__aebi_memcpy`, a call to `__aebi_memcpy4` or machine instructions?)
        
        let elf = ElfFile::new(&self.input.elf_bytes).unwrap();

        if self.target.is_thumb() {
            let sect: SectionHeader = elf.find_section_by_name(".symtab").expect("UNREACHABLE");
            let mut tags: Vec<(u32, thumb::Tag)> = match sect.get_data(&elf).unwrap()
            {
                SectionData::SymbolTable32(entries) => entries
                    .iter()
                    .filter_map(|entry| 
                    {
                        let addr = entry.value() as u32;
                        entry.get_name(&elf).ok().and_then(|name| 
                        {
                            if      name.starts_with("$d") { Some((addr, thumb::Tag::Data)) } 
                            else if name.starts_with("$t") { Some((addr, thumb::Tag::Thumb)) }
                            else                           { None }
                        })
                    })
                    .collect(),
                _ => unreachable!(),
            };

            tags.sort_by(|a, b| a.0.cmp(&b.0));

            if let Some(sect) = elf.find_section_by_name(".text") {
                let stext = sect.address() as u32;
                let text = sect.raw_data(&elf);

                for (address, sym) in &self.symbols.defined {
                    let address = *address as u32;
                    let canonical_name: String = self.aliases[&sym.names[0]].to_string();
                    let mut size = sym.size as u32;

                    if size == 0 {
                        // try harder at finding out the size of this symbol
                        if let Ok(needle) = tags.binary_search_by(|tag| tag.0.cmp(&address)) 
                        {
                            let start = tags[needle];
                            if start.1 == thumb::Tag::Thumb
                            {
                                if let Some(end) = tags.get(needle + 1)
                                {
                                    if end.1 == thumb::Tag::Thumb
                                    {
                                        size = end.0 - start.0;
                                    }
                                }
                            }
                        }
                    }

                    let start = (address - stext) as usize;
                    let end = start + size as usize;
                    let (bls, bs, indirect, modifies_sp, our_stack) = thumb::analyze(
                        &text[start..end],
                        address,
                        self.target == Target::Thumbv7m,
                        &tags,
                    );
                    let caller = self.indices[&canonical_name];

                    // sanity check
                    if let Some(stack) = our_stack
                    {
                        assert_eq!(
                            stack != 0,
                            modifies_sp,
                            "BUG: our analysis reported that `{}` both uses {} bytes of stack and \
                             it does{} modify SP",
                            canonical_name,
                            stack,
                            if !modifies_sp { " not" } else { "" }
                        );
                    }

                    // check the correctness of `modifies_sp` and `our_stack`
                    // also override LLVM's results when they appear to be wrong
                    if let c::Local::Exact(ref mut llvm_stack) = self.g[caller].local
                    {
                        if let Some(stack) = our_stack
                        {
                            if *llvm_stack != stack && self.fns_containing_asm.contains(&canonical_name)
                            {
                                // LLVM's stack usage analysis ignores inline asm, so its results can
                                // be wrong here

                                warn!(
                                    "LLVM reported that `{}` uses {} bytes of stack but \
                                     our analysis reported {} bytes; overriding LLVM's result (function \
                                     uses inline assembly)",
                                    canonical_name, llvm_stack, stack
                                );

                                *llvm_stack = stack;
                            }
                            else if is_outlined_function(&canonical_name)
                            {
                                // ^ functions produced by LLVM's function outliner are not properly
                                // analyzed by LLVM's emit-stack-sizes pass and are all assigned a stack
                                // usage of 0 bytes, which is sometimes wrong
                                if *llvm_stack == 0 && stack != *llvm_stack
                                {
                                    warn!(
                                        "LLVM reported that `{}` uses {} bytes of stack but \
                                         our analysis reported {} bytes; overriding LLVM's result \
                                         (function was produced by LLVM's function outlining pass)",
                                        canonical_name, llvm_stack, stack
                                    );

                                    *llvm_stack = stack;
                                }
                            }
                            else
                            {
                                // in all other cases our results should match
                                if stack != *llvm_stack
                                {
                                    warn!(
                                        "BUG: LLVM reported that `{}` uses {} bytes of stack but \
                                         our analysis reported {} bytes; overriding LLVM's result \
                                         (this should match, it's probably a bug)",
                                        canonical_name, llvm_stack, stack
                                    );

                                    *llvm_stack = stack;
                                }
                                //assert_eq!(
                                //    *llvm_stack, stack,
                                //    "BUG: LLVM reported that `{}` uses {} bytes of stack but \
                                //     this doesn't match our analysis",
                                //    canonical_name, llvm_stack
                                //);
                            }
                        }

                        assert_eq!(
                            *llvm_stack != 0,
                            modifies_sp,
                            "BUG: LLVM reported that `{}` uses {} bytes of stack but this doesn't \
                             match our analysis",
                            canonical_name,
                            *llvm_stack
                        );
                    }
                    else if let Some(stack) = our_stack
                    {
                        self.g[caller].local = c::Local::Exact(stack);
                    }
                    else if !modifies_sp 
                    {
                        // this happens when the function contains intra-branches and our analysis gives
                        // up (`our_stack == None`)
                        self.g[caller].local = c::Local::Exact(0);
                    }

                    if self.g[caller].local == c::Local::Unknown 
                    {
                        warn!("no stack usage information for `{}`", canonical_name);
                    }

                    if !self.defined.contains(&canonical_name) && indirect
                    {
                        // this function performs an indirect function call and we have no type
                        // information to narrow down the list of callees so inject the uncertainty
                        // in the form of a call to an unknown function with unknown stack usage

                        warn!(
                            "`{}` performs an indirect function call and there's \
                             no type information about the operation",
                            canonical_name,
                        );
                        let callee = self.g.add_node( c::Node("?".to_string(), None, false) );
                        self.g.add_edge(caller, callee, ());
                    }

                    let callees_seen = self.edges.entry(caller).or_default();
                    for offset in bls
                    {
                        let addr = (address as i64 + i64::from(offset)) as u64;
                        // address may be off by one due to the thumb bit being set
                        let name = match self.addr2name.get(&addr)
                        {
                            Some(name) => name,
                            None       =>
                            {
                                warn!("BUG? no symbol at address {}", addr);
                                continue;
                            }
                        };

                        let callee = self.indices[name];
                        if !callees_seen.contains(&callee) 
                        {
                            self.g.add_edge(caller, callee, ());
                            callees_seen.insert(callee);
                        }
                    }

                    for offset in bs
                    {
                        let addr = (address as i32 + offset) as u32;

                        if addr >= address && addr < (address + size) 
                        {
                            // intra-function B branches are not function calls
                        } 
                        else 
                        {
                            // address may be off by one due to the thumb bit being set
                            let name = match self.addr2name.get(&(addr as u64))
                            {
                                Some(name) => name,
                                None       =>
                                {
                                    warn!("BUG? no symbol at address {}", addr);
                                    continue
                                },
                            };

                            let callee = self.indices[name];
                            if !callees_seen.contains(&callee) 
                            {
                                self.g.add_edge(caller, callee, ());
                                callees_seen.insert(callee);
                            }
                        }
                    }
                }
            } 
            else 
            {
                error!(".text section not found")
            }
        }
    }
    // Modified fields:
    // - 
    // NOTE: lines 682 - 690
    pub fn warn_for_unmodified_bits(&mut self)
    {
        // add fictitious nodes for indirect function calls
        if self.has_untyped_symbols {
            warn!(
                "the program contains untyped, external symbols (e.g. linked in from binary blobs); \
                 indirect function calls can not be bounded"
            );
        }
    }


    // Modified fields:
    // - g
    // NOTE: lines 691 - 722
    pub fn add_indirect_calls_to_graph(&mut self)
    {
        for (sig, indirect) in &self.indirects
        {
            if !indirect.called 
            {
                continue;
            }

            let callees = &indirect.callees;

            let mut name = sig.to_string();
            // append '*' to denote that this is a function pointer
            name.push('*');

            let call = self.g.add_node( c::Node(name.clone(), Some(0), true));

            for caller in &indirect.callers 
            {
                self.g.add_edge(*caller, call, ());
            }

            if self.has_untyped_symbols 
            {
                // add an edge between this and a potential extern / untyped symbol
                let extern_sym = self.g.add_node( c::Node("?".to_string(), None, false) );
                self.g.add_edge(call, extern_sym, ());
            }
            else
            {
                if callees.is_empty() 
                {
                    error!("BUG? no callees for `{}`", name);
                }
            }

            for callee in callees 
            {
                self.g.add_edge(call, *callee, ());
            }
        }
    }

    // Modified fields:
    // - 
    // NOTE: lines 723 - 789
    pub fn filter_call_graph(&mut self, starting_node: Option<String>)
    {
        if let Some(start) = starting_node
        {
            let start: &str = &start;
            let start = self.indices.get(start).cloned().or_else(|| 
            {
                let start_ = start.to_owned() + "::h";
                let hits = self.indices
                    .keys()
                    .filter_map(|key|
                    {
                        if rustc_demangle::demangle(key)
                            .to_string()
                            .starts_with(&start_)
                        {
                            Some(key)
                        }
                        else
                        {
                            None
                        }
                    })
                    .collect::<Vec<_>>();

                if hits.len() > 1
                {
                    error!("multiple matches for `{}`: {:?}", start, hits);
                    None
                }
                else
                {
                    hits.first().map(|key| self.indices[*key])
                }
            });

            if let Some(start) = start
            {
                  // create a new graph that only contains nodes reachable from `start`
                  let mut g2 = DiGraph::< c::Node, ()>::new();

                  // maps `g`'s `NodeIndex`-es to `g2`'s `NodeIndex`-es
                  let mut one2two = BTreeMap::new();

                  let mut dfs = Dfs::new(&self.g, start);
                  while let Some(caller1) = dfs.next(&self.g) {
                      let caller2 = if let Some(i2) = one2two.get(&caller1) {
                          *i2
                      } else {
                          let i2 = g2.add_node(self.g[caller1].clone());
                          one2two.insert(caller1, i2);
                          i2
                      };

                      let mut callees = self.g.neighbors(caller1).detach();
                      while let Some((_, callee1)) = callees.next(&self.g) {
                          let callee2 = if let Some(i2) = one2two.get(&callee1) {
                              *i2
                          } else {
                              let i2 = g2.add_node(self.g[callee1].clone());
                              one2two.insert(callee1, i2);
                              i2
                          };

                          g2.add_edge(caller2, callee2, ());
                      }
                  }

                  // replace the old graph
                  self.g = g2;

                  // invalidate `indices` to prevent misuse
                  self.indices.clear();
            } 
            else 
            {
                error!("start point not found; the graph will not be filtered")
            }
        }
    }


    // NOTE: lines 790 - 791 is var inits



    // Modified fields:
    // - 
    // NOTE: lines 792 - 871
    pub fn stack_usage_analysis(&mut self)
    {

        if !self.has_stack_usage_info
        {
            error!("The graph has zero stack usage information; skipping max stack usage analysis");
        }
        else if algo::is_cyclic_directed(&self.g)
        {
            let sccs = algo::kosaraju_scc(&self.g);

            // iterate over SCCs (Strongly Connected Components) in reverse topological order
            for scc in &sccs 
            {
                let first = scc[0];

                let is_a_cycle = scc.len() > 1
                    || self.g.neighbors_directed(first, Direction::Outgoing)
                        .any(|n| n == first);

                if is_a_cycle 
                {
                    self.cycles.push(scc.clone());

                    let mut scc_local =
                        c::max_of(scc.iter().map(|node| self.g[*node].local.into())).expect("UNREACHABLE");

                    // the cumulative stack usage is only exact when all nodes do *not* use the stack
                    if let c::Max::Exact(n) = scc_local
                    {
                        if n != 0
                        {
                            scc_local = c::Max::LowerBound(n)
                        }
                    }

                    let neighbors_max = c::max_of(scc.iter().flat_map(|inode| 
                    {
                        self.g.neighbors_directed(*inode, Direction::Outgoing)
                            .filter_map(|neighbor| 
                            {
                                if scc.contains(&neighbor) 
                                {
                                    // we only care about the neighbors of the SCC
                                    None
                                }
                                else
                                {
                                    Some(self.g[neighbor].max.expect("UNREACHABLE"))
                                }
                            })
                    }));

                    for inode in scc
                    {
                        let node = &mut self.g[*inode];
                        if let Some(max) = neighbors_max
                        {
                            node.max = Some(max + scc_local);
                        }
                        else
                        {
                            node.max = Some(scc_local);
                        }
                    }
                }
                else
                {
                    let inode = first;

                    let neighbors_max = c::max_of(
                        self.g.neighbors_directed(inode, Direction::Outgoing)
                            .map(|neighbor| self.g[neighbor].max.expect("UNREACHABLE")),
                    );

                    let node = &mut self.g[inode];
                    if let Some(max) = neighbors_max
                    {
                        node.max = Some(max + node.local);
                    }
                    else
                    {
                        node.max = Some(node.local.into());
                    }
                }
            }
        }
        else
        {
            // compute max stack usage
            let mut topo = Topo::new(Reversed(&self.g));
            while let Some(node) = topo.next(Reversed(&self.g)) {
                debug_assert!(self.g[node].max.is_none());

                let neighbors_max = c::max_of(
                    self.g.neighbors_directed(node, Direction::Outgoing)
                        .map(|neighbor| self.g[neighbor].max.expect("UNREACHABLE")),
                );

                if let Some(max) = neighbors_max
                {
                    self.g[node].max = Some(max + self.g[node].local);
                }
                else 
                {
                    self.g[node].max = Some(self.g[node].local.into());
                }
            }
        }

    }


    // Modified fields:
    // - 
    // NOTE: lines 872 - 882
    pub fn unambiguously_shorten_symbol_names(&mut self)
    {
        for node in self.g.node_weights_mut()
        {
            let demangled = rustc_demangle::demangle(&node.name).to_string();

            if let Some(dehashed) = dehash(&demangled)
            {
                if self.ambiguous[dehashed] == 1
                {
                    node.name = dehashed.to_string();
                }
            }
        }
    }
}


// removes hashes like `::hfc5adc5d79855638`, if present
fn dehash(demangled: &str) -> Option<&str> 
{
    const HASH_LENGTH: usize = 19;

    let len = demangled.as_bytes().len();
    if len > HASH_LENGTH
    {
        if demangled
            .get(len - HASH_LENGTH..)
            .map(|hash| hash.starts_with("::h"))
            .unwrap_or(false)
        {
            Some(&demangled[..len - HASH_LENGTH])
        }
        else 
        {
            None
        }
    }
    else 
    {
        None
    }
}




// LLVM's function outliner pass produces symbols of the form `OUTLINED_FUNCTION_NNN` where `NNN` is
// a monotonically increasing number
fn is_outlined_function(name: &str) -> bool
{
    if let Some(number) = name.strip_prefix("OUTLINED_FUNCTION_")
    {
        u64::from_str_radix(number, 10).is_ok()
    }
    else 
    {
        false
    }
}

