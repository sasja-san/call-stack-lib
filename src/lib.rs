
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(clippy::redundant_field_names)]

pub mod inp;
pub mod ir;
pub mod state;
pub mod thumb;

use petgraph as pg;
// pub mod pg::graph::NodeIndex;









/*      ████████╗ █████╗ ██████╗  ██████╗ ███████╗████████╗       */
/*      ╚══██╔══╝██╔══██╗██╔══██╗██╔════╝ ██╔════╝╚══██╔══╝       */
/*         ██║   ███████║██████╔╝██║  ███╗█████╗     ██║          */
/*         ██║   ██╔══██║██╔══██╗██║   ██║██╔══╝     ██║          */
/*         ██║   ██║  ██║██║  ██║╚██████╔╝███████╗   ██║          */
/*         ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝ ╚═════╝ ╚══════╝   ╚═╝          */
/*     ████████████████████████████████████████████████████╗      */
/*     ╚═══════════════════════════════════════════════════╝      */

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Target {
    Other,
    Thumbv6m,
    Thumbv7m,
}

impl Target {
    pub fn from_str(s: &str) -> Self
    {
        match s
        {
            "thumgvbv6m-none-eabi"    => Target::Thumbv6m,
            "thumbv7m-none-eabi"    => Target::Thumbv7m,
            "thumbv7em-none-eabi"   => Target::Thumbv7m,
            "thumbv7em-none-eabihf" => Target::Thumbv7m,
        _                           => Target::Other,
        }
    }

    pub fn is_thumb(&self) -> bool
    {
        match *self {
            Target::Thumbv6m => true,
            Target::Thumbv7m => true,
            Target::Other    => false,
        }
    }
}











/*      ███╗   ██╗ ██████╗ ██████╗ ███████╗      */
/*      ████╗  ██║██╔═══██╗██╔══██╗██╔════╝      */
/*      ██╔██╗ ██║██║   ██║██║  ██║█████╗        */
/*      ██║╚██╗██║██║   ██║██║  ██║██╔══╝        */
/*      ██║ ╚████║╚██████╔╝██████╔╝███████╗      */
/*      ╚═╝  ╚═══╝ ╚═════╝ ╚═════╝ ╚══════╝      */
/*     ████████████████████████████████████╗     */
/*     ╚═══════════════════════════════════╝     */
use std::borrow::Cow;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node
{
    pub name: String,
    pub local: Local,
    pub max: Option<Max>,
    pub dashed: bool,
}

#[allow(non_snake_case)]
pub fn Node(name: String, stack: Option<u64>, dashed: bool) -> Node
{
    Node
    {
        name: name.into(),
        local: stack.map(Local::Exact).unwrap_or(Local::Unknown),
        max: None,
        dashed,
    }
}












/*      ██╗      ██████╗  ██████╗ █████╗ ██╗           */
/*      ██║     ██╔═══██╗██╔════╝██╔══██╗██║           */
/*      ██║     ██║   ██║██║     ███████║██║           */
/*      ██║     ██║   ██║██║     ██╔══██║██║           */
/*      ███████╗╚██████╔╝╚██████╗██║  ██║███████╗      */
/*      ╚══════╝ ╚═════╝  ╚═════╝╚═╝  ╚═╝╚══════╝      */
/*     ██████████████████████████████████████████╗     */
/*     ╚═════════════════════════════════════════╝     */
use core::fmt;

/// Local stack usage
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Local
{
    Exact(u64),
    Unknown,
}

impl fmt::Display for Local
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result
    {
        match *self
        {
            Local::Exact(n) => write!(f, "{}", n),
            Local::Unknown => f.write_str("?"),
        }
    }
}

impl Into<Max> for Local
{
    fn into(self) -> Max
    {
        match self
        {
            Local::Exact(n) => Max::Exact(n),
            Local::Unknown => Max::LowerBound(0),
        }
    }
}













/*      ███╗   ███╗ █████╗ ██╗  ██╗      */
/*      ████╗ ████║██╔══██╗╚██╗██╔╝      */
/*      ██╔████╔██║███████║ ╚███╔╝       */
/*      ██║╚██╔╝██║██╔══██║ ██╔██╗       */
/*      ██║ ╚═╝ ██║██║  ██║██╔╝ ██╗      */
/*      ╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝      */
/*     ████████████████████████████╗     */
/*     ╚═══════════════════════════╝     */
use core::{ops, cmp};

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum Max
{
    Exact(u64),
    LowerBound(u64),
}

impl ops::Add<Local> for Max {
    type Output = Max;

    fn add(self, rhs: Local) -> Max
    {
        match (self, rhs) {
            (Max::Exact(lhs),      Local::Exact(rhs)) => Max::Exact(lhs + rhs),
            (Max::Exact(lhs),      Local::Unknown)    => Max::LowerBound(lhs),
            (Max::LowerBound(lhs), Local::Exact(rhs)) => Max::LowerBound(lhs + rhs),
            (Max::LowerBound(lhs), Local::Unknown)    => Max::LowerBound(lhs),
        }
    }
}

impl ops::Add<Max> for Max {
    type Output = Max;

    fn add(self, rhs: Max) -> Max {
        match (self, rhs) {
            (Max::Exact(lhs),      Max::Exact(rhs))      => Max::Exact(lhs + rhs),
            (Max::Exact(lhs),      Max::LowerBound(rhs)) => Max::LowerBound(lhs + rhs),
            (Max::LowerBound(lhs), Max::Exact(rhs))      => Max::LowerBound(lhs + rhs),
            (Max::LowerBound(lhs), Max::LowerBound(rhs)) => Max::LowerBound(lhs + rhs),
        }
    }
}

pub fn max_of(mut iter: impl Iterator<Item = Max>) -> Option<Max>
{
    iter.next().map(|first| iter.fold(first, max))
}

pub fn max(lhs: Max, rhs: Max) -> Max
{
    match (lhs, rhs)
    {
        (Max::Exact(lhs),      Max::Exact(rhs))      => Max::Exact(cmp::max(lhs, rhs)),
        (Max::Exact(lhs),      Max::LowerBound(rhs)) => Max::LowerBound(cmp::max(lhs, rhs)),
        (Max::LowerBound(lhs), Max::Exact(rhs))      => Max::LowerBound(cmp::max(lhs, rhs)),
        (Max::LowerBound(lhs), Max::LowerBound(rhs)) => Max::LowerBound(cmp::max(lhs, rhs)),
    }
}

impl fmt::Display for Max
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result 
    {
        match *self 
        {
            Max::Exact(n)      => write!(f, "= {}", n),
            Max::LowerBound(n) => write!(f, ">= {}", n),
        }
    }
}











/*      ██╗███╗   ██╗██████╗ ██╗██████╗ ███████╗ ██████╗████████╗       */
/*      ██║████╗  ██║██╔══██╗██║██╔══██╗██╔════╝██╔════╝╚══██╔══╝       */
/*      ██║██╔██╗ ██║██║  ██║██║██████╔╝█████╗  ██║        ██║          */
/*      ██║██║╚██╗██║██║  ██║██║██╔══██╗██╔══╝  ██║        ██║          */
/*      ██║██║ ╚████║██████╔╝██║██║  ██║███████╗╚██████╗   ██║          */
/*      ╚═╝╚═╝  ╚═══╝╚═════╝ ╚═╝╚═╝  ╚═╝╚══════╝ ╚═════╝   ╚═╝          */
/*     ██████████████████████████████████████████████████████████╗      */
/*     ╚═════════════════════════════════════════════════════════╝      */

use std::collections::{
    BTreeMap,
    HashMap, HashSet,
};

use petgraph::graph::NodeIndex;

// used to track indirect function calls (`fn` pointers)
#[derive(Clone, Default, Debug)]
pub struct Indirect
{
    pub called:  bool,
    pub callers: HashSet<NodeIndex>,
    pub callees: HashSet<NodeIndex>,
}

