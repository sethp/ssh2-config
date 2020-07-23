use core::str::CharIndices;
use std::iter::Peekable;
#[allow(unused)]
use std::str::MatchIndices;

/// Accepts a line and calls the provided closure with exactly one tokenized option.
///
/// It normalizes the tokens into a canonical representation by handling quoted segments
/// and lower-casing the key:
///
/// ```
/// use ssh2_config::option::parse_tokens;
///
/// parse_tokens(r#"OPTION "Hello There""#, |opt, val| {
///     assert_eq!(opt, "option");
///     assert_eq!(val, "Hello There");
///     Ok(())
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
pub fn parse_tokens<T, F>(line: &str, f: F) -> Result<Option<T>, &'static str>
where
    // TODO: better bound
    F: FnOnce(&str, &str) -> Result<T, &'static str>,
    // E: ???,
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
        [] => Ok(None),
        [Word(key), Delim, Word(val)]
        | [Word(key), Delim, Quoted(val)]
        | [Quoted(key), Delim, Word(val)]
        | [Quoted(key), Delim, Quoted(val)] => {
            let k = key.to_ascii_lowercase();
            Ok(Some(f(&k, val)?))
        }
        [Word(k1), Quoted(k2), Delim, Word(val)] | [Word(k1), Quoted(k2), Delim, Quoted(val)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            Ok(Some(f(&k, val)?))
        }
        [Word(key), Delim, Word(v1), Quoted(v2)] | [Quoted(key), Delim, Word(v1), Quoted(v2)] => {
            let k = key.to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(Some(f(&k, &v)?))
        }
        [Word(k1), Quoted(k2), Delim, Word(v1), Quoted(v2)] => {
            let k = format!("{}{}", k1, k2).to_ascii_lowercase();
            let v = format!("{}{}", v1, v2);
            Ok(Some(f(&k, &v)?))
        }
        // TODO: this is not right
        [..] => Err("bad input"),
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

// TODO docs
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'a> {
    Word(&'a str),
    Quoted(&'a str),
    // repeated whitespace or =
    Delim,
    /// Ex. unmatched quote: `"foo` -> `Invalid("foo")`
    Invalid(&'a str),
}

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
            if Tokens::DELIMITERS.contains(ch) || *ch == '"' {
                end = *i;
                break;
            }
            self.chars.next();
        }
        self.last = Some(end);
        Some(Token::Word(&self.line[start..end]))
    }
}

#[cfg(test)]
mod test {
    use super::Token::*;
    use super::{parse_tokens, tokens, Token};
    use itertools::Itertools;

    #[test]
    fn test_tokens() {
        struct TestCase {
            input: &'static str,
            expect: Vec<Token<'static>>,
            message: Option<&'static str>,
        }

        macro_rules! case {
            {input: $left:expr, expect: $right:expr} => ({
                TestCase {
                    input: $left,
                    expect: $right,
                    message: None,
                }
            });
            {input: $left:expr, expect: $right:expr,} => ({
                case!{ input: $left, expect: $right }
            });
            {input: $left:expr, expect: $right:expr, message: $msg:expr} => ({
                TestCase{
                    input: $left,
                    expect: $right,
                    message: Some($msg),
                }
            });
            {input: $left:expr, expect: $right:expr, message: $msg:expr,} => ({
                case!{ input: $left, expect: $right, message: $msg }
            });
        }

        for tc in &[
            case! {
                input: "",
                expect: vec![],
            },
            case! {
                input: "key",
                expect: vec![Word("key")],
            },
            case! {
                input: "key val",
                expect: vec![Word("key"), Delim, Word("val")],
            },
            case! {
                input: "key=val",
                expect: vec![Word("key"), Delim, Word("val")],
            },
            case! {
                input: "=key val",
                expect: vec![Word("key"), Delim, Word("val")],
                message: "tokens should omit leading delimiters",
            },
            case! {
                input: "key val\t\r\x0c",
                expect: vec![Word("key"), Delim, Word("val")],
                message: "tokens should omit trailing blanks",
            },
            case! {
                // TODO: check this against whether ssh finds "garbage" in this case
                input: "key val=",
                expect: vec![Word("key"), Delim, Word("val"), Delim],
                message: "tokens should preserve trailing `=`s",
            },
            case! {
                input: "key \"val\"",
                expect: vec![Word("key"), Delim, Quoted("val")],
            },
            case! {
                input: "w1\"w2\"",
                expect: vec![Word("w1"), Quoted("w2")],
            },
            case! {
                input: "\"w1",
                expect: vec![Invalid("w1")],
            },
            case! {
                input: "\"\"",
                expect: vec![Quoted("")],
            },
        ] {
            let mut out = tokens(tc.input);
            let actual = out.by_ref().take(tc.expect.len() + 1).collect::<Vec<_>>();
            let more = out.next().is_some();

            assert!(
                actual == tc.expect && !more,
                r#"assertion failed: `tokens(input) == expected`
  actual: `[{:?}{}]`,
expected: `{:?}`{}"#,
                actual.iter().format(", "),
                if more { ", .." } else { "" },
                tc.expect,
                tc.message
                    .map(|e| format!(": {}", e))
                    .unwrap_or("".to_string()),
            );
        }
    }

    #[test]
    fn test_tokens_multiline() {
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

         Note: this test is intended to be more descriptive than normative."#
        );
    }

    #[test]
    fn test_parse_tokens() {
        let opt = parse_tokens("", |_, _| Ok(())).expect("parse_failed");
        assert!(opt.is_none());

        for spelling in &[
            "Hello World",
            "=Hello World",
            "HeLlO World",
            "HEllo       World",
            "HEllo  \"World\"",
            "\"HEllo\"  \"World\"",
            "H\"Ello\"  World",
            "H\"Ello\"  \"World\"",
            "HEllo  Wo\"rld\"",
            "\"HEllo\"  Wo\"rld\"",
            "HE\"llo\"  Wo\"rld\"",
        ] {
            parse_tokens(spelling, |k, v| Ok(assert_eq!((k, v), ("hello", "World"))))
                .expect("parse failed")
                .expect("nothing found");
        }

        parse_tokens("h\"el lo  \"       wo\" rld\"", |k, v| {
            Ok(assert_eq!((k, v), ("hel lo  ", "wo rld")))
        })
        .expect("parse failed")
        .expect("nothing found");

        parse_tokens::<(), _>("a b", |_, _| Err("thanks I hate it"))
            .expect_err("wanted parse error");

        for invalid in &[
            "hello",
            "hello world zzz",
            "h\"ello",
            "h\"ello    world zzz",
            "h\"ello\"  wo\"rld\"zzz",
            "h\"ello\"  wo\"rld\" zzz",
            "h\"ello\"\"\" world",
        ] {
            parse_tokens("h\"ello", |_, _| Ok(()))
                .expect_err(format!("wanted parse error for input {:?}", invalid).as_ref());
        }
    }
}
