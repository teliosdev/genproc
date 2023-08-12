#[derive(Copy, Clone, Hash)]
pub struct Span<'i> {
    pub input: &'i str,
    start: u32,
    // end: usize,
    length: u32,
}

impl std::fmt::Debug for Span<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Span")
            .field(&self.as_str())
            .field(&(self.start..self.end()))
            .finish()
    }
}

impl std::fmt::Display for Span<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end())
    }
}

impl PartialEq for Span<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.input, other.input)
            && self.start == other.start
            && self.length == other.length
    }
}

impl Eq for Span<'_> {}

impl<'i> Span<'i> {
    pub fn new(input: &'i str, start: u32, length: u32) -> Self {
        debug_assert!((start + length) as usize <= input.len());
        Span {
            input,
            start,
            length,
        }
    }

    pub fn start(&self) -> u32 {
        self.start
    }

    pub fn end(&self) -> u32 {
        self.start + self.length
    }

    pub fn as_str(&self) -> &'i str {
        &self.input[(self.start as usize)..(self.end() as usize)]
    }

    pub fn merge(self, other: Self) -> Self {
        let start = self.start.min(other.start);
        let length = self.length.max(other.length);
        Span {
            input: self.input,
            start,
            length,
        }
    }
}

impl<'i> std::ops::BitOr for Span<'i> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.merge(rhs)
    }
}
