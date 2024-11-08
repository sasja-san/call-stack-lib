use std::io;

// #[derive(Clone)]
pub struct Escaper<W>
where
    W: io::Write,
{
    pub writer: W,
    pub error: io::Result<usize>,
}


impl<W> Escaper<W>
where
    W: io::Write,
{
    pub fn new(writer: W) -> Self {
        Escaper {
            writer,
            error: Ok(0),
        }
    }
}


impl<W> io::Write for Escaper<W>
where 
    W: io::Write
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize>
    {
        let mut bw: usize = buf.len(); // bytes written
        for &c in buf
        {
            if c == b'"' // prepend quote marks with backslash
            {
                self.error = self.writer.write( b"\\" ); // NOTE: magic @ here
                bw += 1;
                if self.error.is_err() { return Err(io::Error::last_os_error()); }
            }

            self.error = self.writer.write( &[c] );
            if self.error.is_err() { return Err(io::Error::last_os_error()); }
        }
        Ok( bw )
    }

    fn flush(&mut self) -> Result<(), std::io::Error>
    {
        self.writer.flush()
    }
}

