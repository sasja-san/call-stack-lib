use petgraph::Graph;
use std::{
    io,
    io::Write as _, // to get write_fmt, granting writeln!
};

use crate as c;
use crate::state::State;
use crate::output::escaper::Escaper;


impl State
{
    pub fn output_top(&self, mut writer: impl io::Write) -> io::Result<()>
    {
        let g: &Graph<c::Node, ()> = &self.g;

        assert!(g.is_directed());

        let mut nodes: Vec<c::Node> = Vec::new();
        for node in g.raw_nodes().iter() {
            nodes.push(node.weight.clone());
        }

        // Locate max
        if let Some(max) = c::max_of(nodes.iter().map(|n| n.max.unwrap_or(c::Max::Exact(0)))) {
            writeln!(
                writer,
                "{} MAX",
                match max {
                    c::Max::Exact(n)      => n,
                    c::Max::LowerBound(n) => n,
                }
            )?;
        }

        writeln!(writer, "Usage Function")?;

        nodes.sort_by(|a, b| {
            let a: u64 = if let c::Local::Exact(n) = a.local { n } else { 0 };
            let b: u64 = if let c::Local::Exact(n) = b.local { n } else { 0 };
            b.cmp(&a)
        });

        let mut esc = Escaper::new(writer); // ownership is trash (see original)

        for node in nodes.iter() {
            let name = rustc_demangle::demangle(&node.name);
            let val: u64 = if let c::Local::Exact(n) = node.local {
                n
            } else {
                0
            };

            write!(esc, "{} ", val)?; // isn't supposed to be Escaper 
            writeln!(esc, "{}", name)?;

            // esc.error?; // .clone()?;
        }
        Ok(())
    }
}



