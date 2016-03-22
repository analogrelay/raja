use std::fmt;

// Tendril limits us to 32-bit here anyway
// Plus, a 4GB text file is craziness ;P (famous last words)
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub struct TextLocation {
    pub line: u32,
    pub column: u32,
    pub offset: u32
}

impl TextLocation {
    pub fn new(line: u32, column: u32, offset: u32) -> TextLocation {
        TextLocation {
            line: line,
            column: column,
            offset: offset
        }
    }

    pub fn advance(&self, ch: char) -> TextLocation {
        match ch {
            '\n' => TextLocation::new(self.line + 1, 0, self.offset + 1),
            x => TextLocation::new(self.line, self.column + 1, self.offset + 1)
        }
    }
}

impl fmt::Display for TextLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "({}, {}; {})", self.line, self.column, self.offset)
    }
}
