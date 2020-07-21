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

use crate::{EOL_WHITESPACE, WHITESPACE};

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
    // Unmatched quote: "foo -> Invalid("foo")
    Invalid(&'a str),
}

use core::str::CharIndices;
use std::iter::Peekable;
#[allow(unused)]
use std::str::MatchIndices;
// TODO: Tokens/TokensInternal?

#[derive(Debug)]
pub struct Tokens<'a> {
    line: &'a str,
    // TODO: MatchIndices?
    // matcher: MatchIndices<'a, &'static [char]>,
    // last_match: Option<(usize, &'a str)>,
    chars: Peekable<CharIndices<'a>>,
    last: Option<usize>,
}

impl<'a> Tokens<'a> {
    // TODO: more kinds of blanks
    // const CHARS: &'static [char] = &[' '];
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        if let Some((_, ' ')) = self.chars.peek() {
            while let Some((i, ' ')) = self.chars.peek() {
                self.last = Some(i + ' '.len_utf8());
                self.chars.next();
            }
            return Some(Token::Delim);
        }
        let start = self.last.unwrap_or(0);
        if let Some((_, '"')) = self.chars.peek() {
            let start = start + '"'.len_utf8();
            self.chars.next();
            while let Some((_, ch)) = self.chars.peek() {
                if *ch == '"' {
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
            if *ch == ' ' || *ch == '"' {
                end = *i;
                break;
            }
            self.chars.next();
        }
        self.last = Some(end);
        // TODO: empty quoted tokens?
        if start < end {
            Some(Token::Word(&self.line[start..end]))
        } else {
            None
        }
    }
}

// TODO for pub: what happens if it's multiple lines?
pub fn tokens<'a>(line: &'a str) -> Tokens {
    let line = line
        .trim_start_matches(WHITESPACE)
        .trim_end_matches(EOL_WHITESPACE);
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
