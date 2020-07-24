use core::str::CharIndices;
use std::fmt;
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
/// information on these, see [TODO] and [`Token`].
///
/// [TODO]: link to the parse / FromStr impl?
/// [Token]: crate::option::Token
pub fn parse_tokens<T, F, E>(line: &str, f: F) -> Result<Option<T>, Error>
where
    F: FnOnce(&str, &str) -> Result<T, E>,
    Error: From<E>,
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
        [..] => Err(Error::TODO),
    }
}

/// Error represents the ways parsing an ssh config option can fail.
///
/// Broadly there are two "kinds" of failure: a failure specific to parsing the option,
/// or a failure to make sense of the config statement as a whole. These are, respectively, represented
/// by the `Err` variant, and the other variants.
#[derive(Debug)]
pub enum Error {
    TODO,

    /// Missing argument, ex. `Port`
    MissingArgument,
    /// Unmatched quote, ex. `GlobalKnownHostsFile "/etc/ssh/ssh_known_hosts /etc/ssh/ssh_known_hosts2`
    UnmatchedQuote,
    // TODO: it's a context-sensitive grammar for UserKnownHostsFile, GlobalKnownHostsFile, and RekeyLimit.
    /// Trailing arguments, ex. `Port 22 tcp`
    TrailingGarbage(String),

    /// A contextually specific error, ex. `Port -1`
    Err(DetailedError),
}

/// DetailedError represents the various kinds of contextual failures possible when parsing an
/// individual option.
///
/// The broadest categories are `UnsupportedOption` and `BadOption` which refer to known-invalid
/// and unknown options respectively. Whether the other variants are possible depends on which
/// keyword begins the line.
#[derive(Debug)]
#[non_exhaustive]
pub enum DetailedError {
    UnsupportedOption(String),
    BadOption(String),

    InvalidPort(std::num::ParseIntError),
}

impl std::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::TODO => write!(f, "TODO"),

            Error::MissingArgument => write!(f, "missing argument"),
            Error::UnmatchedQuote => write!(f, "no matching `\"` found"),
            Error::TrailingGarbage(ref garbage) => write!(f, "garbage at end of line: {}", garbage),

            Error::Err(ref err) => write!(f, "bad option: {}", err),
        }
    }
}

impl std::error::Error for DetailedError {}

impl fmt::Display for DetailedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DetailedError::*;
        match *self {
            UnsupportedOption(ref opt) => write!(f, "Unsupported option: {:?}", opt),
            BadOption(ref opt) => write!(f, "Bad option: {:?}", opt),

            InvalidPort(ref err) => write!(f, "invalid port: {}", err),
        }
    }
}

/// `tokens` converts a string into an iterator of [`Token`s], intended for use with [`str::lines`].
///
/// These token streams are not complete, choosing to omit beginning- and end-of-line blank characters as
/// these have no semantic importance to the format. For more details on the SSH option format, see [`Token`]
/// and [TODO].
///
/// [`Token`s]: crate::option::Token
/// [`Token`]: crate::option::Token
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
        chars: line.char_indices().peekable(),
    }
}

/// A token found in the ssh config language.
///
/// As we are unaware of any formal grammar for the ssh config language, this is an approximation
/// of the minimum elements necessary to handle some of the stranger, but accepted, expressions.
///
/// Notably, the "delimiter" token is explicitly included because both `w1 "w2"` and `w1"w2"`
/// are valid but have different meanings: the former is a complete config statement, declaring the
/// value for option `w1` to be `w2`, whereas the latter is a valid config fragment expressing the
/// single phrase `w1w2` that may be used either as an option name or value.
///
/// In order to tell these two cases apart, we include a literal `Delim` tokens in the stream:
///
/// ```
/// use ssh2_config::option::{tokens, Token};
///
/// assert_eq!(
///     tokens(r#"w1 "w2""#)
///         .collect::<Vec<_>>(),
///     vec![Token::Word("w1"), Token::Delim, Token::Quoted("w2")]
/// );
///
/// assert_eq!(
///     tokens(r#"w1"w2""#)
///         .collect::<Vec<_>>(),
///     vec![Token::Word("w1"), Token::Quoted("w2")]
/// );
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'a> {
    Word(&'a str),
    Quoted(&'a str),
    /// repeated whitespace or =
    Delim,
    /// Ex. unmatched quote: `"foo` -> `Invalid("foo")`
    Invalid(&'a str),
    // TODO Comment
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
        match self.chars.peek()? {
            (_, ch) if Tokens::DELIMITERS.contains(ch) => {
                while let Some((_, ch)) = self.chars.peek() {
                    if !Tokens::DELIMITERS.contains(ch) {
                        break;
                    }
                    self.chars.next();
                }
                Some(Token::Delim)
            }
            (start, '"') => {
                let start = start + '"'.len_utf8();
                self.chars.next();
                while let Some((_, ch)) = self.chars.peek() {
                    if *ch == '"' || *ch == '\n' {
                        break;
                    }
                    self.chars.next();
                }
                if let Some((i, _)) = self.chars.peek() {
                    let end = *i;
                    let ch = self.chars.next().unwrap().1;
                    let tok = &self.line[start..end];
                    Some(if ch == '"' {
                        Token::Quoted(tok)
                    } else {
                        Token::Invalid(tok)
                    })
                } else {
                    Some(Token::Invalid(&self.line[start..]))
                }
            }
            (start, _) => {
                let start = *start;
                let mut end = self.line.len();
                while let Some((i, ch)) = self.chars.peek() {
                    if Tokens::DELIMITERS.contains(ch) || *ch == '"' {
                        end = *i;
                        break;
                    }
                    self.chars.next();
                }
                Some(Token::Word(&self.line[start..end]))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::Token::*;
    use super::{parse_tokens, tokens, Error, Token};
    use itertools::Itertools;

    impl From<&str> for Error {
        fn from(_: &str) -> Error {
            Error::TODO
        }
    }

    impl From<()> for Error {
        fn from(_: ()) -> Error {
            unimplemented!()
        }
    }

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

        assert_eq!(
            tokens("\"hello\r\nworld").take(3).collect::<Vec<_>>(),
            vec![Invalid("hello\r"), Word("world")],
            r#"
        We make minor exception to the "`tokens` treats end of line characters as any other word
         character" rule for handling unterminated quotes: we'd like to avoid giving the impression,
         even in an error case, that strings in ssh configs can span multiple lines."#
        );
    }

    #[test]
    fn test_parse_tokens() {
        let opt = parse_tokens::<_, _, ()>("", |_, _| Ok(())).expect("parse_failed");
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
            parse_tokens::<_, _, ()>(spelling, |k, v| Ok(assert_eq!((k, v), ("hello", "World"))))
                .expect("parse failed")
                .expect("nothing found");
        }

        parse_tokens::<_, _, ()>("h\"el lo  \"       wo\" rld\"", |k, v| {
            Ok(assert_eq!((k, v), ("hel lo  ", "wo rld")))
        })
        .expect("parse failed")
        .expect("nothing found");
    }

    #[test]
    fn test_parse_tokens_err() {
        parse_tokens::<(), _, _>("a b", |_, _| Err("thanks I hate it"))
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
            parse_tokens::<_, _, ()>("h\"ello", |_, _| Ok(()))
                .expect_err(format!("wanted parse error for input {:?}", invalid).as_ref());
        }
    }
}
