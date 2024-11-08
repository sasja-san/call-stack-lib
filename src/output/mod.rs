
// re-exporting functions
mod top;     // pub use top;
mod dot;     pub use dot::DotConf;
mod escaper; pub use escaper::*;

#[derive( PartialEq, Debug, Clone, Copy)]
pub enum OutputFormat {
    Dot,
    Top,
}


