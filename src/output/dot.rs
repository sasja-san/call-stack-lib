use petgraph::{Graph, graph::NodeIndex};
use std::{
    io,
    io::Write as _, // to get write_fmt, granting writeln!
};

use crate as c;
use crate::state::State;
use crate::output::escaper::Escaper;





impl State
{
    pub fn output_dot(&self, mut writer: impl io::Write, dc: DotConf) -> io::Result<()>
    {
        let g:      &Graph<c::Node, ()>     = &self.g;
        let cycles: &Vec< Vec<NodeIndex> >  = &self.cycles;

        writeln!(writer, "digraph {{")?;
        writeln!(writer, "    node [fontname={} shape=box]", &dc.font)?;

        for (i, node) in g.raw_nodes().iter().enumerate() {
            let node = &node.weight;

            write!(writer, "    {} [label=\"", i,)?;

            let mut esc = Escaper::new(&mut writer);
            write!(esc, "{}", rustc_demangle::demangle(&node.name))?;
            esc.error?;

            if let Some(max) = node.max {
                write!(writer, "\\nmax {}", max)?;
            }

            write!(writer, "\\nlocal = {}\"", node.local,)?;

            if node.dashed {
                write!(writer, " style=dashed")?;
            }

            writeln!(writer, "]")?;
        }

        for edge in g.raw_edges() {
            writeln!(
                writer,
                "    {} -> {}",
                edge.source().index(),
                edge.target().index()
            )?;
        }

        for (i, cycle) in cycles.iter().enumerate() {
            writeln!(writer, "\n    subgraph cluster_{} {{", i)?;
            writeln!(writer, "        style=dashed")?;
            writeln!(writer, "        fontname={}", &dc.font)?;
            writeln!(writer, "        label=\"SCC{}\"", i)?;

            for node in cycle {
                writeln!(writer, "        {}", node.index())?;
            }

            writeln!(writer, "    }}")?;
        }

        writeln!(writer, "}}")?;

        Ok(())
    }



}



pub struct DotConf
{
    pub font: String,
}

impl DotConf
{
    pub fn default() -> Self
    {
        DotConf
        {
            font: "monospace".to_string(),
        }
    }
}


