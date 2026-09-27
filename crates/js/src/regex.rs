//! Own regex engine (strict JS subset): pattern parser + backtracking
//! matcher with a fuel cap. No backrefs, no lookarounds, no named groups.
//! Flags: i m s g. Works on chars, reports byte ranges for slicing.

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Flags {
    pub global: bool,
    pub ignore_case: bool,
    pub multiline: bool,
    pub dot_all: bool,
}

pub fn parse_flags(s: &str) -> Result<Flags, char> {
    let mut f = Flags {
        global: false,
        ignore_case: false,
        multiline: false,
        dot_all: false,
    };
    for c in s.chars() {
        match c {
            'g' => f.global = true,
            'i' => f.ignore_case = true,
            'm' => f.multiline = true,
            's' => f.dot_all = true,
            other => return Err(other),
        }
    }
    Ok(f)
}

#[derive(Debug, Clone, PartialEq)]
enum Node {
    Empty,
    Lit(char),
    Dot,
    Class {
        neg: bool,
        ranges: Vec<(char, char)>,
    },
    AnchorStart,
    AnchorEnd,
    WordBound(bool),
    Concat(Vec<Node>),
    Alt(Vec<Node>),
    Quant {
        lo: usize,
        hi: Option<usize>,
        lazy: bool,
        child: Box<Node>,
    },
    Group {
        idx: usize,
        child: Box<Node>,
    },
}

#[derive(Debug, Clone)]
pub struct Compiled {
    root: Node,
    pub groups: usize,
    pub flags: Flags,
    pub source: String,
}

pub fn compile(source: &str, flags: &str) -> Result<Compiled, String> {
    let fl = parse_flags(flags).map_err(|c| format!("invalid flag '{c}'"))?;
    let mut p = P {
        c: source.chars().collect(),
        i: 0,
        groups: 0,
    };
    let root = p.alt(false)?;
    if p.i != p.c.len() {
        return Err(format!("trailing characters at {}", p.i));
    }
    Ok(Compiled {
        root,
        groups: p.groups,
        flags: fl,
        source: source.to_string(),
    })
}

struct P {
    c: Vec<char>,
    i: usize,
    groups: usize,
}

impl P {
    fn peek(&self) -> Option<char> {
        self.c.get(self.i).copied()
    }

    fn alt(&mut self, in_group: bool) -> Result<Node, String> {
        let mut branches = vec![self.concat(in_group)?];
        while self.peek() == Some('|') {
            self.i += 1;
            branches.push(self.concat(in_group)?);
        }
        Ok(if branches.len() == 1 {
            branches.pop().unwrap()
        } else {
            Node::Alt(branches)
        })
    }

    fn concat(&mut self, in_group: bool) -> Result<Node, String> {
        let mut parts = Vec::new();
        while let Some(ch) = self.peek() {
            if ch == '|' || (ch == ')' && in_group) {
                break;
            }
            parts.push(self.quant(in_group)?);
        }
        Ok(match parts.len() {
            0 => Node::Empty,
            1 => parts.pop().unwrap(),
            _ => Node::Concat(parts),
        })
    }

    fn quant(&mut self, in_group: bool) -> Result<Node, String> {
        let atom = self.atom(in_group)?;
        let (lo, hi) = match self.peek() {
            Some('*') => {
                self.i += 1;
                (0, None)
            }
            Some('+') => {
                self.i += 1;
                (1, None)
            }
            Some('?') => {
                self.i += 1;
                (0, Some(1))
            }
            Some('{') => match self.counted()? {
                Some(q) => q,
                None => return Ok(atom),
            },
            _ => return Ok(atom),
        };
        let lazy = if self.peek() == Some('?') {
            self.i += 1;
            true
        } else {
            false
        };
        Ok(Node::Quant {
            lo,
            hi,
            lazy,
            child: Box::new(atom),
        })
    }

    /// `{n}`, `{n,}`, `{n,m}`. None when not a valid counted form, in
    /// which case `{` stays unconsumed (treated as a literal).
    fn counted(&mut self) -> Result<Option<(usize, Option<usize>)>, String> {
        let save = self.i;
        self.i += 1; // '{'
        let mut n: usize = 0;
        let mut digits = 0;
        while let Some(d) = self.peek().filter(|c| c.is_ascii_digit()) {
            n = n
                .saturating_mul(10)
                .saturating_add((d as usize) - ('0' as usize));
            self.i += 1;
            digits += 1;
        }
        if digits == 0 {
            self.i = save;
            return Ok(None);
        }
        if self.peek() == Some('}') {
            self.i += 1;
            return Ok(Some((n, Some(n))));
        }
        if self.peek() != Some(',') {
            self.i = save;
            return Ok(None);
        }
        self.i += 1;
        if self.peek() == Some('}') {
            self.i += 1;
            return Ok(Some((n, None)));
        }
        let mut m: usize = 0;
        let mut digits = 0;
        while let Some(d) = self.peek().filter(|c| c.is_ascii_digit()) {
            m = m
                .saturating_mul(10)
                .saturating_add((d as usize) - ('0' as usize));
            self.i += 1;
            digits += 1;
        }
        if digits == 0 || self.peek() != Some('}') {
            self.i = save;
            return Ok(None);
        }
        self.i += 1;
        if m < n {
            return Err(format!("numbers out of order in {{{n},{m}}}"));
        }
        Ok(Some((n, Some(m))))
    }

    fn atom(&mut self, in_group: bool) -> Result<Node, String> {
        let ch = self.peek().ok_or("pattern ended mid-atom")?;
        match ch {
            '(' => {
                self.i += 1;
                if self.peek() == Some('?') {
                    self.i += 1;
                    if self.peek() != Some(':') {
                        return Err("only (?: ) groups are supported".into());
                    }
                    self.i += 1;
                    let inner = self.alt(true)?;
                    self.expect(')')?;
                    Ok(inner)
                } else {
                    self.groups += 1;
                    let idx = self.groups;
                    let inner = self.alt(true)?;
                    self.expect(')')?;
                    Ok(Node::Group {
                        idx,
                        child: Box::new(inner),
                    })
                }
            }
            '[' => self.class(),
            '.' => {
                self.i += 1;
                Ok(Node::Dot)
            }
            '^' => {
                self.i += 1;
                Ok(Node::AnchorStart)
            }
            '$' => {
                self.i += 1;
                Ok(Node::AnchorEnd)
            }
            ')' if in_group => Err("unmatched ')'".into()),
            '\\' => self.escape(false),
            _ => {
                self.i += 1;
                Ok(Node::Lit(ch))
            }
        }
    }

    fn expect(&mut self, ch: char) -> Result<(), String> {
        if self.peek() == Some(ch) {
            self.i += 1;
            Ok(())
        } else {
            Err(format!("expected '{ch}'"))
        }
    }

    fn escape(&mut self, in_class: bool) -> Result<Node, String> {
        self.i += 1; // '\\'
        let ch = self.peek().ok_or("trailing \\")?;
        self.i += 1;
        match ch {
            'd' => Ok(class_of(&[('0', '9')], false)),
            'D' => Ok(class_of(&[('0', '9')], true)),
            'w' => Ok(class_of(
                &[('A', 'Z'), ('a', 'z'), ('0', '9'), ('_', '_')],
                false,
            )),
            'W' => Ok(class_of(
                &[('A', 'Z'), ('a', 'z'), ('0', '9'), ('_', '_')],
                true,
            )),
            's' => Ok(class_of(
                &[
                    (' ', ' '),
                    ('\t', '\t'),
                    ('\n', '\n'),
                    ('\r', '\r'),
                    ('\u{c}', '\u{c}'),
                    ('\u{b}', '\u{b}'),
                ],
                false,
            )),
            'S' => Ok(class_of(
                &[
                    (' ', ' '),
                    ('\t', '\t'),
                    ('\n', '\n'),
                    ('\r', '\r'),
                    ('\u{c}', '\u{c}'),
                    ('\u{b}', '\u{b}'),
                ],
                true,
            )),
            'b' if !in_class => Ok(Node::WordBound(true)),
            'B' if !in_class => Ok(Node::WordBound(false)),
            'n' => Ok(Node::Lit('\n')),
            't' => Ok(Node::Lit('\t')),
            'r' => Ok(Node::Lit('\r')),
            'f' => Ok(Node::Lit('\u{c}')),
            'v' => Ok(Node::Lit('\u{b}')),
            '0' => Ok(Node::Lit('\0')),
            'x' => {
                let h = self.hex(2)?;
                Ok(Node::Lit(char::from_u32(h).unwrap_or('\u{FFFD}')))
            }
            'u' => {
                let h = self.hex(4)?;
                Ok(Node::Lit(char::from_u32(h).unwrap_or('\u{FFFD}')))
            }
            c if c.is_ascii_digit() => Err("backreferences are unsupported".into()),
            c => Ok(Node::Lit(c)),
        }
    }

    fn hex(&mut self, n: usize) -> Result<u32, String> {
        let mut h = 0u32;
        for _ in 0..n {
            match self.peek() {
                Some(c) if c.is_ascii_hexdigit() => {
                    h = h * 16 + c.to_digit(16).unwrap();
                    self.i += 1;
                }
                _ => return Err("bad hex escape".into()),
            }
        }
        Ok(h)
    }

    fn class(&mut self) -> Result<Node, String> {
        self.i += 1; // '['
        let neg = if self.peek() == Some('^') {
            self.i += 1;
            true
        } else {
            false
        };
        let mut ranges: Vec<(char, char)> = Vec::new();
        let mut first = true;
        loop {
            match self.peek() {
                None => return Err("unterminated class".into()),
                Some(']') if !first => {
                    self.i += 1;
                    break;
                }
                Some(_) => {
                    let lo = self.class_atom()?;
                    if self.peek() == Some('-') && self.c.get(self.i + 1) != Some(&']') {
                        self.i += 1; // '-'
                        let hi = self.class_atom()?;
                        if (hi as u32) < (lo as u32) {
                            return Err("range out of order".into());
                        }
                        ranges.push((lo, hi));
                    } else {
                        ranges.push((lo, lo));
                    }
                }
            }
            first = false;
        }
        Ok(Node::Class { neg, ranges })
    }

    fn class_atom(&mut self) -> Result<char, String> {
        match self.peek() {
            None => Err("unterminated class".into()),
            Some('\\') => {
                let save = self.i;
                match self.escape(true)? {
                    Node::Lit(c) => Ok(c),
                    _ => {
                        self.i = save;
                        Err("class range over a class escape".into())
                    }
                }
            }
            Some(c) => {
                self.i += 1;
                Ok(c)
            }
        }
    }
}

fn class_of(ranges: &[(char, char)], neg: bool) -> Node {
    Node::Class {
        neg,
        ranges: ranges.to_vec(),
    }
}

// ---- matcher ------------------------------------------------------------

// ---- matcher ------------------------------------------------------------
// All-results matcher: each node yields every (end, captures) outcome in
// preference order (greedy-first). Callers try outcomes head-first, which
// gives real backtracking: a failed tail resumes the quantifier with
// fewer reps. Fuel bounds total work.

fn is_word(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn eq_ci(a: char, b: char) -> bool {
    if a == b {
        return true;
    }
    if a.is_ascii() && b.is_ascii() {
        return a.eq_ignore_ascii_case(&b);
    }
    a.to_lowercase().eq(b.to_lowercase())
}

fn in_class(ranges: &[(char, char)], neg: bool, c: char, fl: &Flags) -> bool {
    let mut hit = false;
    for &(lo, hi) in ranges {
        if fl.ignore_case {
            if lo <= c && c <= hi {
                hit = true;
                break;
            }
            // ASCII fast fold for ranges.
            if lo.is_ascii() && hi.is_ascii() && c.is_ascii() {
                let c = c.to_ascii_lowercase();
                if lo.to_ascii_lowercase() <= c && c <= hi.to_ascii_lowercase() {
                    hit = true;
                    break;
                }
            } else if c
                .to_lowercase()
                .any(|l| ranges.iter().any(|&(a, b)| a <= l && l <= b))
            {
                hit = true;
                break;
            }
        } else if lo <= c && c <= hi {
            hit = true;
            break;
        }
    }
    hit != neg
}

fn at_line_start(s: &[char], pos: usize) -> bool {
    pos == 0 || matches!(s[pos - 1], '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

fn at_line_end(s: &[char], pos: usize) -> bool {
    pos == s.len() || matches!(s[pos], '\n' | '\r' | '\u{2028}' | '\u{2029}')
}

pub const MAX_DEPTH: u32 = 256;
const MAX_OUTCOMES: usize = 4096;

type Caps = Vec<Option<(usize, usize)>>;
type Outs = Vec<(usize, Caps)>;

struct Run<'a> {
    fl: &'a Flags,
    fuel: u64,
    depth: u32,
}

fn burn(run: &mut Run) -> bool {
    if run.fuel == 0 || run.depth > MAX_DEPTH {
        return false;
    }
    run.fuel -= 1;
    true
}

fn mt(n: &Node, s: &[char], pos: usize, caps: Caps, run: &mut Run) -> Outs {
    if !burn(run) {
        return vec![];
    }
    match n {
        Node::Empty => vec![(pos, caps)],
        Node::Lit(a) => match s.get(pos) {
            Some(&c)
                if (run.fl.ignore_case && eq_ci(*a, c)) || (!run.fl.ignore_case && *a == c) =>
            {
                vec![(pos + 1, caps)]
            }
            _ => vec![],
        },
        Node::Dot => match s.get(pos) {
            Some(&c) if c == '\n' || c == '\r' => {
                if run.fl.dot_all {
                    vec![(pos + 1, caps)]
                } else {
                    vec![]
                }
            }
            Some(_) => vec![(pos + 1, caps)],
            None => vec![],
        },
        Node::Class { neg, ranges } => match s.get(pos) {
            Some(&c) if in_class(ranges, *neg, c, run.fl) => vec![(pos + 1, caps)],
            _ => vec![],
        },
        Node::AnchorStart => {
            if pos == 0 || (run.fl.multiline && at_line_start(s, pos)) {
                vec![(pos, caps)]
            } else {
                vec![]
            }
        }
        Node::AnchorEnd => {
            if pos == s.len() || (run.fl.multiline && at_line_end(s, pos)) {
                vec![(pos, caps)]
            } else {
                vec![]
            }
        }
        Node::WordBound(want) => {
            let left = pos > 0 && is_word(s[pos - 1]);
            let right = pos < s.len() && is_word(s[pos]);
            if (left != right) == *want {
                vec![(pos, caps)]
            } else {
                vec![]
            }
        }
        Node::Concat(parts) => {
            let mut cur = vec![(pos, caps)];
            for part in parts {
                let mut next = Outs::new();
                for (p, c) in cur {
                    if next.len() >= MAX_OUTCOMES || !burn(run) {
                        return next;
                    }
                    next.extend(mt(part, s, p, c, run));
                    if next.len() > MAX_OUTCOMES {
                        next.truncate(MAX_OUTCOMES);
                    }
                }
                cur = next;
                if cur.is_empty() {
                    break;
                }
            }
            cur
        }
        Node::Alt(branches) => {
            let mut out = Outs::new();
            for b in branches {
                if out.len() >= MAX_OUTCOMES || !burn(run) {
                    break;
                }
                out.extend(mt(b, s, pos, caps.clone(), run));
            }
            out.truncate(MAX_OUTCOMES);
            out
        }
        Node::Group { idx, child } => {
            let mut out = Outs::new();
            for (end, mut c) in mt(child, s, pos, caps, run) {
                if *idx < c.len() {
                    c[*idx] = Some((pos, end));
                }
                out.push((end, c));
                if out.len() >= MAX_OUTCOMES {
                    break;
                }
            }
            out
        }
        Node::Quant {
            lo,
            hi,
            lazy,
            child,
        } => {
            // Levels[count] = all outcomes of exactly `count` reps.
            let mut levels: Vec<Outs> = vec![vec![(pos, caps)]];
            loop {
                let count = levels.len();
                if let Some(h) = hi {
                    if count > *h {
                        break;
                    }
                }
                if !burn(run) {
                    break;
                }
                let mut next = Outs::new();
                let mut progressed = false;
                for (p, c) in levels[count - 1].iter() {
                    for (end, cc) in mt(child, s, *p, c.clone(), run) {
                        if end != *p {
                            progressed = true;
                        }
                        next.push((end, cc));
                        if next.len() >= MAX_OUTCOMES {
                            break;
                        }
                    }
                    if next.len() >= MAX_OUTCOMES {
                        break;
                    }
                }
                if next.is_empty() || !progressed {
                    // No reps possible, or only empty reps (stop rather
                    // than looping forever; Annex-B empty semantics lite).
                    if !next.is_empty() && count == 1 {
                        levels.push(next);
                    }
                    break;
                }
                levels.push(next);
                if levels.len() > 65536 {
                    break;
                }
            }
            let mut out = Outs::new();
            if *lazy {
                for (k, level) in levels.iter().enumerate() {
                    if k < *lo {
                        continue;
                    }
                    out.extend(level.clone());
                    if out.len() >= MAX_OUTCOMES {
                        break;
                    }
                }
            } else {
                for (k, level) in levels.iter().enumerate().rev() {
                    if k < *lo {
                        continue;
                    }
                    out.extend(level.clone());
                    if out.len() >= MAX_OUTCOMES {
                        break;
                    }
                }
            }
            out.truncate(MAX_OUTCOMES);
            out
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Match {
    pub start: usize,
    pub end: usize,
    /// Byte ranges per capture group (group 0 excluded).
    pub groups: Vec<Option<(usize, usize)>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuelOut;

/// Leftmost match at or after `from_byte`. Byte offsets in the result.
pub fn exec_from(
    c: &Compiled,
    text: &str,
    from_byte: usize,
    fuel: u64,
) -> Result<Option<Match>, FuelOut> {
    let chars: Vec<char> = text.chars().collect();
    let bytes: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    let to_char = |b: usize| -> usize {
        if b >= text.len() {
            return chars.len();
        }
        match bytes.binary_search(&b) {
            Ok(i) => i,
            Err(i) => i,
        }
    };
    let to_byte = |cpos: usize| -> usize {
        if cpos >= chars.len() {
            text.len()
        } else {
            bytes[cpos]
        }
    };
    let from = to_char(from_byte);
    // Fast path: anchored start without multiline only tries `from`.
    let anchored = matches!(c.root, Node::Concat(ref parts)
        if matches!(parts.first(), Some(Node::AnchorStart)))
        || matches!(c.root, Node::AnchorStart);
    let mut starts: Vec<usize> = Vec::new();
    if anchored && !c.flags.multiline {
        starts.push(from.min(chars.len()));
    } else {
        starts.extend(from..=chars.len());
    }
    let mut run = Run {
        fl: &c.flags,
        fuel,
        depth: 0,
    };
    for st in starts {
        let caps: Caps = vec![None; c.groups + 1];
        let outs = mt(&c.root, &chars, st, caps, &mut run);
        if let Some((end, caps)) = outs.into_iter().next() {
            let groups = caps
                .iter()
                .skip(1)
                .map(|g| g.map(|(a, b)| (to_byte(a), to_byte(b))))
                .collect();
            return Ok(Some(Match {
                start: to_byte(st),
                end: to_byte(end),
                groups,
            }));
        }
        if run.fuel == 0 {
            return Err(FuelOut);
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(pat: &str, flags: &str, text: &str) -> Option<(usize, usize)> {
        let c = compile(pat, flags).unwrap();
        exec_from(&c, text, 0, 1_000_000)
            .unwrap()
            .map(|m| (m.start, m.end))
    }

    fn g(pat: &str, flags: &str, text: &str) -> Vec<Option<(usize, usize)>> {
        let c = compile(pat, flags).unwrap();
        exec_from(&c, text, 0, 1_000_000)
            .unwrap()
            .map(|m| m.groups)
            .unwrap_or_default()
    }

    #[test]
    fn fyscal_patterns() {
        assert_eq!(m(r"<([^>]+@[^>]+)>", "", "a<b@c>d"), Some((1, 6)));
        assert_eq!(m(r"[,;]", "", "a;b"), Some((1, 2)));
        assert_eq!(m(r"-", "g", "a-b"), Some((1, 2)));
        assert_eq!(m(r"text\/plain|text\/html", "i", "TEXT/HTML"), Some((0, 9)));
        assert_eq!(m(r"\d{4,8}", "", "ab12345c"), Some((2, 7)));
        assert_eq!(m(r"\bword\b", "", "a word b"), Some((2, 6)));
    }

    #[test]
    fn groups_and_lazy() {
        assert_eq!(
            g(r"(\w+)@(\w+)", "", "u@d"),
            vec![Some((0, 1)), Some((2, 3))]
        );
        assert_eq!(m(r"a+?", "", "aaa"), Some((0, 1)));
        assert_eq!(m(r"a+", "", "aaa"), Some((0, 3)));
        assert_eq!(m(r"(?:ab)+", "", "ababx"), Some((0, 4)));
    }

    #[test]
    fn anchors_and_flags() {
        assert_eq!(m(r"^b", "m", "a\nb"), Some((2, 3)));
        assert_eq!(m(r"^b", "", "a\nb"), None);
        assert_eq!(m(r"a$", "", "a\na"), Some((2, 3)));
        assert_eq!(m(r".", "s", "\n"), Some((0, 1)));
        assert_eq!(m(r".", "", "\n"), None);
    }

    #[test]
    fn annex_b_tolerance() {
        assert_eq!(m(r"a)", "", "a)"), Some((0, 2)));
        assert_eq!(m(r"a{,2}", "", "a{,2}"), Some((0, 5)));
        assert_eq!(m(r"a{2}", "", "aaa"), Some((0, 2)));
    }

    #[test]
    fn errors() {
        assert!(compile(r"(a", "").is_err());
        assert!(compile(r"[a", "").is_err());
        assert!(compile(r"a{2,1}", "").is_err());
        assert!(compile(r"\1", "").is_err());
        assert!(compile(r"(?a)", "").is_err());
        assert!(compile(r"a", "y").is_err());
    }

    #[test]
    fn fuel_caps_catastrophe() {
        let c = compile(r"(a|a)*b", "").unwrap();
        assert!(exec_from(&c, &"a".repeat(200), 0, 50_000).is_err());
    }
}
