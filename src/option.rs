// How could this stuff be maintained? Feature gates and matrix builds?

pub fn parse_always_alloc(line: &str) -> Result<(String, String), &'static str> {
    // TODO: longest possible key?
    const L: usize = 20;
    const WHITESPACE: &[char] = &[
        ' ', '\t', '\r', '\n', /* for convenience, treat as blank */ '=',
    ];
    const QUOTE: char = '"';
    let mut key = String::with_capacity(L);
    let mut val = String::with_capacity(line.len());
    let mut is_quoted = false;
    let mut quote_ok = true;
    let mut key_done = false;
    let mut val_found = false;
    let mut garbage = false;
    for c in line.chars() {
        if c == QUOTE {
            if !is_quoted && !quote_ok {
                garbage = true;
                break;
            }
            is_quoted = !is_quoted;
            quote_ok = false;
            continue;
        } else if !is_quoted && WHITESPACE.contains(&c) {
            if key_done && val_found {
                garbage = true;
                break;
            }
            key_done = true;
            quote_ok = true;
            continue;
        }

        if !quote_ok && !is_quoted && val_found {
            garbage = true;
            break;
        }

        if !key_done {
            key.push(c.to_ascii_lowercase())
        } else {
            val_found = true;
            val.push(c)
        }
    }

    if !key_done {
        Err("no argument")
    } else if is_quoted {
        Err("no matching quote")
    } else if garbage {
        Err("garbage at eol")
    } else {
        Ok((key, val))
    }
}

#[test]
fn test_parse_always_alloc() {
    assert_eq!(
        parse_always_alloc("heLlO world").expect("parse error"),
        (String::from("hello"), String::from("world"))
    );
    assert_eq!(
        parse_always_alloc("hello       world").expect("parse error"),
        (String::from("hello"), String::from("world"))
    );
    assert_eq!(
        parse_always_alloc("\"hello\"       \"world\"").expect("parse error"),
        (String::from("hello"), String::from("world"))
    );
    assert_eq!(
        parse_always_alloc("h\"ello\"       wo\"rld\"").expect("parse error"),
        (String::from("hello"), String::from("world"))
    );
    assert_eq!(
        parse_always_alloc("h\"ello  \"       wo\" rld\"").expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_always_alloc("h\"ello").expect_err("wanted parse error");
    parse_always_alloc("h\"ello       world zzz").expect_err("wanted parse error");
    parse_always_alloc("h\"ello\"       wo\"rld\"zzz").expect_err("wanted parse error");
    parse_always_alloc("h\"ello\"       wo\"rld\" zzz").expect_err("wanted parse error");
    parse_always_alloc("h\"ello\"\"\" world").expect_err("wanted parse error");
}

use crate::{EOL_WHITESPACE, QUOTE, WHITESPACE};

pub fn parse_regex_onig_split<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    // for<'b> F: FnOnce(&'b str, &'b str) -> T,
    F: FnOnce(&str, &str) -> T,
{
    use onig::Regex;

    lazy_static! {
        // Split on quotes or whitespace that is preceded by an even number of quotes (zero is even)
        static ref RE: Regex =
            Regex::new(r#"(?<=^(?:(?:[^"]*"){2})*[^"]*)[ \t\r\n=]+|(?=")|(?<=")"#).unwrap();
    }
    const QUOTE: &str = "\"";

    // TODO: is 9 enough?
    match RE
        .splitn(
            line.trim_start_matches(WHITESPACE)
                .trim_end_matches(EOL_WHITESPACE),
            9,
        )
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .as_slice()
    {
        // TODO: more cases
        [key, val] | [key, QUOTE, val, QUOTE] | [QUOTE, key, QUOTE, QUOTE, val, QUOTE] => {
            let k = key.to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [k1, QUOTE, k2, QUOTE, val] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [k1, QUOTE, k2, QUOTE, v1, QUOTE, v2, QUOTE] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [..] => Err("bad input"),
    }
}

#[test]
fn test_onig() {
    use onig::Regex;
    assert_eq!(
        Regex::new(r#"[ ]+"#)
            .unwrap()
            .split(" a\"b")
            .collect::<Vec<_>>(),
        vec!["", "a\"b"]
    );
    assert_eq!(
        Regex::new(r#"(?=")"#)
            .unwrap()
            .split(" a\"b")
            .collect::<Vec<_>>(),
        vec![" a", "\"b"]
    );
    assert_eq!(
        Regex::new(r#"(?<=")"#)
            .unwrap()
            .split(" a\"b")
            .collect::<Vec<_>>(),
        vec![" a\"", "b"]
    );
    // assert_eq!(
    //     Regex::new(r#"(?=")|(?<=")| +"#)
    //         .unwrap()
    //         .split(" a\"b")
    //         .collect::<Vec<_>>(),
    //     vec!["", "a", "\"", "b"]
    // );

    let re = Regex::new(r#"(?=|)|(?<=|)| "#).unwrap();
    let result = re.find_iter(" a,b");
    for mat in result {
        println!("{:?}", mat);
    }
    assert_eq!(
        Regex::new(r#"(?=#)|(?<=#)| +"#)
            .unwrap()
            .split(" a#b")
            .collect::<Vec<_>>(),
        vec!["", "a", "#", "b"]
    );
}

#[test]
fn test_parse_regex_onig_split() {
    parse_regex_onig_split("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_regex_onig_split("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_onig_split("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_onig_split("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_onig_split("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_onig_split("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_onig_split("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_onig_split("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_regex_onig_split("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_regex_onig_split("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_regex_onig_split("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_onig_split("h\"ello\"       wo\"rld\"zzz", |_, _| ())
        .expect_err("wanted parse error");
    parse_regex_onig_split("h\"ello\"       wo\"rld\" zzz", |_, _| ())
        .expect_err("wanted parse error");
    parse_regex_onig_split("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}

pub fn parse_regex_groups<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    F: FnOnce(&str, &str) -> T,
{
    use regex::Regex;
    lazy_static! {
        static ref RE: Regex =
            Regex::new(r#"^(?P<key>\w+|\w*"[^"]*")[ \t\r\n=]+(?P<val>\w+|\w*"[^"]*")$"#).unwrap();
    }

    let m = RE
        .captures_iter(
            line.trim_start_matches(WHITESPACE)
                .trim_end_matches(EOL_WHITESPACE),
        )
        .next()
        .ok_or("no matches")?;

    let k = match &m["key"]
        .splitn(3, '"')
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .as_slice()
    {
        [k] => k.to_ascii_lowercase(),
        [k1, k2] => format!("{}{}", k1, k2).to_ascii_lowercase(),
        [..] => unreachable!(),
    };
    match &m["val"]
        .splitn(3, '"')
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .as_slice()
    {
        [v] => Ok(f(&k, &v)),
        [v1, v2] => {
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [..] => unreachable!(),
    }
}

#[test]
fn test_parse_regex_groups() {
    parse_regex_groups("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_regex_groups("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_groups("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_groups("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_groups("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_groups("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_groups("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_groups("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_regex_groups("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_regex_groups("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_regex_groups("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_groups("h\"ello\"       wo\"rld\"zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_groups("h\"ello\"       wo\"rld\" zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_groups("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}

pub fn parse_regex_ladder<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    F: FnOnce(&str, &str) -> T,
{
    use regex::Regex;
    lazy_static! {
        // L0 is the simplest and most commonly found pattern by far
        static ref RE_L0: Regex =
        Regex::new(r#"^(?P<key>\w+)[ \t\r\n=]+(?P<val>\w+)$"#).unwrap();
        // L1 includes a quoted config value, which is rarely required or used
        static ref RE_L1: Regex =
        Regex::new(r#"^(?P<key>\w+) +"?(?P<val>\w+)"?$"#).unwrap();
        // L2 accepts the full language of the openssh binary (as well as repeated `=` delimiters, which the latter rejects).
        // This including quoting the second portion of a key or value which seems exceedingly rare
        static ref RE_L2: Regex =
            Regex::new(r#"^(?P<key>\w+|\w*"[^"]*")[ \t\r\n=]+(?P<val>\w+|\w*"[^"]*")$"#).unwrap();
    }

    let line = line
        .trim_start_matches(WHITESPACE)
        .trim_end_matches(EOL_WHITESPACE);
    let m = RE_L0
        .captures_iter(line)
        .next()
        .or_else(|| RE_L1.captures_iter(line).next());

    if let Some(cap) = m {
        let k = cap["key"].to_ascii_lowercase();
        Ok(f(&k, &cap["val"]))
    } else {
        RE_L2
            .captures_iter(line)
            .next()
            .map(|m| {
                let k = match &m["key"]
                    .splitn(3, '"')
                    .filter(|s| !s.is_empty())
                    .collect::<Vec<_>>()
                    .as_slice()
                {
                    [k] => k.to_ascii_lowercase(),
                    [k1, k2] => format!("{}{}", k1, k2).to_ascii_lowercase(),
                    [..] => unreachable!(),
                };
                match &m["val"]
                    .splitn(3, '"')
                    .filter(|s| !s.is_empty())
                    .collect::<Vec<_>>()
                    .as_slice()
                {
                    [v] => Ok(f(&k, &v)),
                    [v1, v2] => {
                        let v = format!("{}{}", v1, v2);
                        Ok(f(&k, &v))
                    }
                    [..] => unreachable!(),
                }
            })
            .unwrap_or(Err("no matches"))
    }
}

#[test]
fn test_parse_regex_ladder() {
    parse_regex_ladder("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_regex_ladder("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_ladder("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_ladder("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_ladder("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_ladder("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_regex_ladder("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_regex_ladder("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_regex_ladder("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_regex_ladder("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_regex_ladder("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_ladder("h\"ello\"       wo\"rld\"zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_ladder("h\"ello\"       wo\"rld\" zzz", |_, _| ()).expect_err("wanted parse error");
    parse_regex_ladder("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'a> {
    Word(&'a str),
    Quoted(&'a str),
    // repeated whitespace or =
    Delim,
    /// Ex. unmatched quote: `"foo` -> `Invalid("foo")`
    Invalid(&'a str),
}

use core::str::CharIndices;
use std::iter::Peekable;
#[allow(unused)]
use std::str::MatchIndices;

/// An iterator of [`Token`]s created with the method [`tokens`].
///
/// [`Token`]: crate::option::Token
/// [`tokens`]: crate::option::tokens
#[derive(Debug)]
pub struct Tokens<'a> {
    line: &'a str,
    // TODO: MatchIndices?
    // matcher: MatchIndices<'a, &'static [char]>,
    // last_match: Option<(usize, &'a str)>,
    chars: Peekable<CharIndices<'a>>,
    last: Option<usize>,
}

/// Option tokenizer.
impl<'a> Tokens<'a> {
    /// Delimiters separate other tokens in a line. Repeated instances of delimiters will be collapsed
    /// into a single [`Token::Delim`][0].
    ///
    /// For more details, see [strdelim_internal in misc.c][1].
    ///
    /// [0]: crate::Token::Delim
    /// [1]: https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L329
    pub const DELIMITERS: &'static [char] = &[
        ' ', '\t', '=', /* for convenience we accept even when there's more than one */
    ];

    /// Blanks are a superset of Delimiters that are considered "ignorable," but only when they appear at
    /// the beginning of a line.
    ///
    /// Note that we differ from [upstream] by omitting the newline `'\n'` character from this set.
    ///
    /// [upstream]: https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L323-L325
    pub const BLANK: &'static [char] = &[' ', '\t', '\r', '=' /* treat as blank */];

    /// EOL blanks are a superset of Blanks that are "ignorable" at the end of a line.
    ///
    /// Notably this includes the "form feed" character, as well as repeated carriage returns. We don't include
    /// the newline (`'\n'`) character in this set, however.
    ///
    /// See also: [readconfig.c].
    ///
    /// [readconfig.c]: https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L916-L923
    pub const EOL_BLANK: &'static [char] = &[' ', '\t', '\r', '\x0c' /* form feed */];
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        let (_, ch) = self.chars.peek()?;
        if Tokens::DELIMITERS.contains(ch) {
            while let Some((i, ch)) = self.chars.peek() {
                if !Tokens::DELIMITERS.contains(ch) {
                    break;
                }
                self.last = Some(i + ch.len_utf8());
                self.chars.next();
            }
            return Some(Token::Delim);
        }
        let start = self.last.unwrap_or(0);
        if *ch == '"' {
            let start = start + '"'.len_utf8();
            self.chars.next();
            while let Some((_, ch)) = self.chars.peek() {
                // TODO: test and/or docs
                if *ch == '"' || *ch == '\n' || *ch == '\r' {
                    break;
                }
                self.chars.next();
            }
            if let Some((i, '"')) = self.chars.peek() {
                let end = *i;
                self.chars.next();
                self.last = Some(end + '"'.len_utf8());
                return Some(Token::Quoted(&self.line[start..end]));
            } else {
                self.last = Some(self.line.len());
                return Some(Token::Invalid(&self.line[start..]));
            }
        }
        let mut end = self.line.len();
        while let Some((i, ch)) = self.chars.peek() {
            if Tokens::DELIMITERS.contains(ch) || *ch == QUOTE {
                end = *i;
                break;
            }
            self.chars.next();
        }
        self.last = Some(end);
        if start < end {
            Some(Token::Word(&self.line[start..end]))
        } else {
            None
        }
    }
}

/// `tokens` converts a string into an iterator of [`Token`s], intended for use with [`str::lines`].
///
/// These token streams are not complete, choosing to omit beginning- and end-of-line blank characters as
/// these have no semantic importance to the format. For more details on the SSH option format, see [TODO]
///
/// [`Token`s]: crate::option::Token
/// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
/// [TODO]: link to the parse / FromStr impl?
///
/// # Example
///
/// ```
/// use ssh2_config::option::{tokens, Token};
///
/// assert_eq!(
///     tokens(r#"key="value""#)
///         .collect::<Vec<_>>(),
///     vec![Token::Word("key"), Token::Delim, Token::Quoted("value")]
/// );
///
/// assert_eq!(
///     tokens(r#"  key    val"ue"  "#)
///         .collect::<Vec<_>>(),
///     vec![Token::Word("key"), Token::Delim, Token::Word("val"), Token::Quoted("ue")]
/// );
/// ```
///
/// In the second example, notice that the blank characters at the beginning and end of the line are omitted.
///
/// # A note on multi-line strings
///
/// No ssh option can span multiple lines, so it's best to split before tokenizing each line individually
/// in order to ensure proper handling of "end of line" blank delimiters like carriage returns and line feeds:
///
/// ```
/// use ssh2_config::option;
/// use ssh2_config::option::Token;
///
/// assert_eq!(
///     "hello\x0c\nworld"
///         .lines()
///         .flat_map(option::tokens)
///         .collect::<Vec<_>>(),
///     vec![Token::Word("hello"), Token::Word("world")]
/// );
/// ```
///
pub fn tokens(line: &str) -> Tokens {
    let line = line
        .trim_start_matches(Tokens::BLANK)
        .trim_end_matches(Tokens::EOL_BLANK);
    Tokens {
        line: line,
        // matcher: line.match_indices(Tokens::CHARS),
        // last_match: None,
        last: None,
        chars: line.char_indices().peekable(),
    }
}

#[test]
fn test_tokens() {
    use Token::*;
    assert_eq!(tokens("").take(2).collect::<Vec<_>>(), vec![]);
    assert_eq!(tokens("key").take(3).collect::<Vec<_>>(), vec![Word("key")]);
    assert_eq!(
        tokens("key val").take(4).collect::<Vec<_>>(),
        vec![Word("key"), Delim, Word("val")]
    );
    assert_eq!(
        tokens("=key val").take(4).collect::<Vec<_>>(),
        vec![Word("key"), Delim, Word("val")]
    );
    assert_eq!(
        tokens("key    val").take(5).collect::<Vec<_>>(),
        vec![Word("key"), Delim, Word("val")],
        "iterator should collapse repeated blanks into a single Delim token",
    );
    assert_eq!(
        tokens("key    \"val\"").take(5).collect::<Vec<_>>(),
        vec![Word("key"), Delim, Quoted("val")],
    );
    assert_eq!(
        tokens("w1\"w2\"").take(5).collect::<Vec<_>>(),
        vec![Word("w1"), Quoted("w2")],
    );
    assert_eq!(
        tokens("\"w1").take(5).collect::<Vec<_>>(),
        vec![Invalid("w1")],
    );
    assert_eq!(tokens("\"\"").take(5).collect::<Vec<_>>(), vec![Quoted("")],);

    assert_eq!(
        tokens("key=val").take(4).collect::<Vec<_>>(),
        vec![Word("key"), Delim, Word("val")]
    );

    assert_eq!(
        tokens("hello\n=world").take(3).collect::<Vec<_>>(),
        vec![Word("hello\n"), Delim, Word("world")]
    );
}

#[test]
fn test_tokens_multiline() {
    use Token::*;

    assert_eq!(
        tokens("hello\x0c\nworld\x0c\r\r\n")
            .take(3)
            .collect::<Vec<_>>(),
        vec![Word("hello\x0c\nworld\x0c\r\r\n")],
        r#"
        As no ssh option can span multiple lines, `tokens` expects to operate on lines individually,
         so we currently look for "end of line" characters to be treated as any normal "word"
         character, unless they appear at the end of the input. See the docs for `tokens` for more
         examples on usage.

         Note: this test is more descriptive than normative."#
    )
}

pub fn parse_tokens<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    F: FnOnce(&str, &str) -> T,
{
    use Token::*;
    match tokens(line)
        .take(6 /* one longer than the longest valid pattern */)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [Word(key), Delim, Word(val)]
        | [Word(key), Delim, Quoted(val)]
        | [Quoted(key), Delim, Word(val)]
        | [Quoted(key), Delim, Quoted(val)] => {
            let k = key.to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [Word(k1), Quoted(k2), Delim, Word(val)] | [Word(k1), Quoted(k2), Delim, Quoted(val)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [Word(key), Delim, Word(v1), Quoted(v2)] | [Quoted(key), Delim, Word(v1), Quoted(v2)] => {
            let k = key.to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [Word(k1), Quoted(k2), Delim, Word(v1), Quoted(v2)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [..] => Err("bad input"),
    }
}

#[test]
fn test_parse_tokens() {
    parse_tokens("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_tokens("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("h\"ello\" \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("hello w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens("\"hello\" w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_tokens("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_tokens("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_tokens("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens("h\"ello\"       wo\"rld\"zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens("h\"ello\"       wo\"rld\" zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}

pub fn parse_tokens_no_vec<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    F: FnOnce(&str, &str) -> T,
{
    use Token::*;

    let mut toks = tokens(line);

    match (
        toks.next(),
        toks.next(),
        toks.next(),
        toks.next(),
        toks.next(),
        toks.next(),
    ) {
        (Some(Word(key)), Some(Delim), Some(Word(val)), None, None, None)
        | (Some(Word(key)), Some(Delim), Some(Quoted(val)), None, None, None)
        | (Some(Quoted(key)), Some(Delim), Some(Word(val)), None, None, None)
        | (Some(Quoted(key)), Some(Delim), Some(Quoted(val)), None, None, None) => {
            let k = key.to_ascii_lowercase();
            Ok(f(&k, val))
        }
        (Some(Word(k1)), Some(Quoted(k2)), Some(Delim), Some(Word(val)), None, None)
        | (Some(Word(k1)), Some(Quoted(k2)), Some(Delim), Some(Quoted(val)), None, None) => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            Ok(f(&k, val))
        }
        (Some(Word(key)), Some(Delim), Some(Word(v1)), Some(Quoted(v2)), None, None)
        | (Some(Quoted(key)), Some(Delim), Some(Word(v1)), Some(Quoted(v2)), None, None) => {
            let k = key.to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        (Some(Word(k1)), Some(Quoted(k2)), Some(Delim), Some(Word(v1)), Some(Quoted(v2)), None) => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        (..) => Err("bad input"),
    }
}

#[test]
fn test_parse_tokens_no_vec() {
    parse_tokens_no_vec("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_tokens_no_vec("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("h\"ello\" \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("hello w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec("\"hello\" w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_tokens_no_vec("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_tokens_no_vec("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_tokens_no_vec("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens_no_vec("h\"ello\"       wo\"rld\"zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens_no_vec("h\"ello\"       wo\"rld\" zzz", |_, _| ())
        .expect_err("wanted parse error");
    parse_tokens_no_vec("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}

/// Accepts a line and calls the provided closure with exactly one tokenized option.
///
/// It normalizes the tokens into a canonical representation by handling quoted segments
/// and lower-casing the key:
///
/// ```
/// use ssh2_config::option::parse_tokens_no_vec2;
///
/// parse_tokens_no_vec2(r#"OPTION "Hello There""#, |opt, val| {
///     assert_eq!(opt, "option");
///     assert_eq!(val, "Hello There");
/// });
/// ```
///
/// Note that, since all of the known ssh option keywords are exclusively in the ASCII character space,
/// we avoid handling of arbitrary unicode code points in the key portion of the line.
///
/// Note also that there are some unexpected arrangements of tokens that ssh will accept. For more
/// information on these, see [TODO].
///
/// [TODO]: link to the parse / FromStr impl?
pub fn parse_tokens_no_vec2<T, F>(line: &str, f: F) -> Result<T, &'static str>
where
    F: FnOnce(&str, &str) -> T,
{
    use Token::*;

    let mut toks = [Delim; 6 /* one longer than the longest valid pattern */];
    // with thanks to the collect_slice crate
    let n = toks
        .iter_mut()
        .zip(tokens(line))
        .fold(0, |count, (dest, item)| {
            *dest = item;
            count + 1
        });

    match toks[..n] {
        [Word(key), Delim, Word(val)]
        | [Word(key), Delim, Quoted(val)]
        | [Quoted(key), Delim, Word(val)]
        | [Quoted(key), Delim, Quoted(val)] => {
            let k = key.to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [Word(k1), Quoted(k2), Delim, Word(val)] | [Word(k1), Quoted(k2), Delim, Quoted(val)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            Ok(f(&k, val))
        }
        [Word(key), Delim, Word(v1), Quoted(v2)] | [Quoted(key), Delim, Word(v1), Quoted(v2)] => {
            let k = key.to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [Word(k1), Quoted(k2), Delim, Word(v1), Quoted(v2)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(f(&k, &v))
        }
        [..] => Err("bad input"),
    }
}

#[test]
fn test_parse_tokens_no_vec2() {
    parse_tokens_no_vec2("heLlO world", |k, v| assert_eq!((k, v), ("hello", "world")))
        .expect("parse error");
    parse_tokens_no_vec2("=hello world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("hello       world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("hello       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("\"hello\"       \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec2("h\"ello\" world", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("h\"ello\" \"world\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("hello w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");
    parse_tokens_no_vec2("\"hello\" w\"orld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec2("h\"ello\"       wo\"rld\"", |k, v| {
        assert_eq!((k, v), ("hello", "world"))
    })
    .expect("parse error");

    parse_tokens_no_vec2("h\"el lo  \"       wo\" rld\"", |k, v| {
        assert_eq!((k, v), ("hel lo  ", "wo rld"))
    })
    .expect("parse error");

    // just to be sure this isn't all for naught
    assert_eq!(
        parse_tokens_no_vec2("h\"ello  \"       wo\" rld\"", |k, v| {
            (k.to_string(), v.to_string())
        })
        .expect("parse error"),
        (String::from("hello  "), String::from("wo rld"))
    );

    parse_tokens_no_vec2("h\"ello", |_, _| ()).expect_err("wanted parse error");
    parse_tokens_no_vec2("h\"ello       world zzz", |_, _| ()).expect_err("wanted parse error");
    parse_tokens_no_vec2("h\"ello\"       wo\"rld\"zzz", |_, _| ())
        .expect_err("wanted parse error");
    parse_tokens_no_vec2("h\"ello\"       wo\"rld\" zzz", |_, _| ())
        .expect_err("wanted parse error");
    parse_tokens_no_vec2("h\"ello\"\"\" world", |_, _| ()).expect_err("wanted parse error");
}
