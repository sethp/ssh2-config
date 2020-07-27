// TODO:
// #![warn(missing_docs)]
#![cfg_attr(test, deny(warnings))]

use core::str::CharIndices;
use std::fmt;
use std::iter::Peekable;
#[allow(unused)]
use std::str::MatchIndices;

#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SSHOption {
    User(String),
    Port(u16),
}

impl std::str::FromStr for SSHOption {
    type Err = Error;

    // TODO multi-line?
    // TODO: docs (?)
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // TODO: it's a context-sensitive grammar for UserKnownHostsFile, GlobalKnownHostsFile, and RekeyLimit.
        use SSHOption::*;
        match parse_tokens(s, |keyword, next| match keyword {
            "user" => Tokens::with_one_arg(next, |arg| Ok(User(arg.to_owned()))),
            "port" => Tokens::with_one_arg(next, |arg| {
                Ok(Port(arg.parse().map_err(DetailedError::InvalidPort)?))
            }),
            _ => Err(Error::from(DetailedError::BadOption(keyword.to_string()))),
        })
        .transpose()
        {
            Some(res) => res,
            None => todo!(),
        }
    }
}

/// Accepts a line and calls the provided closure with exactly one tokenized option.
///
/// It normalizes the tokens into a canonical representation by handling quoted segments,
/// and lower-casing the key:
///
/// ```
/// use ssh2_config::option::{Error, parse_tokens, Token, Tokens};
///
/// parse_tokens::<_, _, Error>(r#""OPTION" "Hello There""#, |opt, tokens| {
///     assert_eq!(opt, "option");
///     assert_eq!(tokens.next(), Some(Token::Quoted("Hello There")));
///     Ok(())
/// })
/// .expect("parse failed")
/// .expect("nothing found");
/// ```
///
/// `parse_tokens` will also check that all of the tokens from the line are fully consumed, as does ssh.
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
    F: FnOnce(&str, &mut dyn Iterator<Item = Token>) -> Result<T, E>,
    Error: From<E>,
{
    let mut toks = itertools::put_back(tokens(line));
    let first = toks.next();
    if let None = first {
        return Ok(None);
    }
    toks.put_back(first.unwrap());

    let res = Tokens::with_args(&mut toks, |k, toks| Ok(f(&k.to_ascii_lowercase(), toks)?))?;

    match toks.next() {
        None => Ok(Some(res)),
        // something something never leave a delim at beginning of stream
        Some(Token::Delim) => unreachable!(),
        Some(Token::Word(s)) | Some(Token::Quoted(s)) => Err(Error::TrailingGarbage(s.to_owned())),
        Some(Token::Invalid(s)) => Err(Error::UnmatchedQuote(s.to_owned())),
    }
}

/// Error represents the ways parsing an ssh config option can fail.
///
/// Broadly there are two "kinds" of failure: a failure specific to parsing the option,
/// or a failure to make sense of the config statement as a whole. These are, respectively, represented
/// by the `Err` variant, and the other variants.
#[derive(Debug)]
pub enum Error {
    /// Missing argument, ex. `Port`
    MissingArgument,
    /// Unmatched quote, ex. `GlobalKnownHostsFile "/etc/ssh/ssh_known_hosts /etc/ssh/ssh_known_hosts2`
    UnmatchedQuote(String),
    /// Trailing arguments, ex. `Port 22 tcp`
    TrailingGarbage(String),

    /// A contextually specific error, ex. `Port -1`
    Detailed(DetailedError),
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
            Error::MissingArgument => write!(f, "missing argument"),
            Error::UnmatchedQuote(ref invalid) => {
                write!(f, "no matching `\"` found: \"{}", invalid)
            }
            Error::TrailingGarbage(ref garbage) => {
                write!(f, "garbage at end of line, starting at: {}", garbage)
            }

            Error::Detailed(ref err) => write!(f, "{}", err),
        }
    }
}

impl std::error::Error for DetailedError {}

impl fmt::Display for DetailedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DetailedError::*;
        match *self {
            UnsupportedOption(ref opt) => write!(f, "unsupported option: {:?}", opt),
            BadOption(ref opt) => write!(f, "bad option: {:?}", opt),

            InvalidPort(ref err) => write!(f, "invalid port: {}", err),
        }
    }
}

impl From<DetailedError> for Error {
    fn from(e: DetailedError) -> Self {
        Error::Detailed(e)
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
    // TODO Comment?
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

    /// EOL blanks are a distinct set of characters that are "ignorable" at the end of a line.
    ///
    /// Notably this includes the "form feed" character, as well as repeated carriage returns. We don't include
    /// the newline (`'\n'`) character in this set, however.
    ///
    /// See also: [readconfig.c].
    ///
    /// [readconfig.c]: https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L916-L923
    pub const EOL_BLANK: &'static [char] = &[' ', '\t', '\r', '\x0c' /* form feed */];

    pub fn with_one_arg<T, F>(toks: &mut dyn Iterator<Item = Token<'a>>, f: F) -> Result<T, Error>
    where
        F: FnOnce(&str) -> Result<T, Error>,
    {
        Tokens::with_args(toks, |a, _| f(a))
    }

    // comparable to strdelim
    pub fn with_args<T, F>(toks: &mut dyn Iterator<Item = Token<'a>>, f: F) -> Result<T, Error>
    where
        F: FnOnce(&str, &mut dyn Iterator<Item = Token<'a>>) -> Result<T, Error>,
    {
        use Token::*;

        match toks.next() {
            None => Err(Error::MissingArgument),
            Some(Word(w)) => match toks.next() {
                None | Some(Delim) => f(w, toks),
                Some(Quoted(q)) => {
                    let arg = format!("{}{}", w, q);
                    match toks.next() {
                        None | Some(Delim) => f(&arg, toks),
                        Some(next @ Word(_)) | Some(next @ Quoted(_)) => {
                            f(&arg, &mut itertools::put_back(toks).with_value(next))
                        }
                        Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
                    }
                }
                // We can't see back-to-back word tokens
                Some(Word(_)) => unreachable!(),
                Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
            },
            Some(Quoted(w)) => match toks.next() {
                None | Some(Delim) => f(w, toks),
                Some(next @ Quoted(_)) | Some(next @ Word(_)) => {
                    f(w, &mut itertools::put_back(toks).with_value(next))
                }
                Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
            },

            // We can't start with a Delim token, and the invariant is that we never leave a Delim at the
            // beginning of the stream
            Some(Delim) => unreachable!("invalid Delim at beginning of token stream"),
            Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
        }
    }
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
    use super::SSHOption;
    use super::Token::*;
    use super::{parse_tokens, tokens, Error, Token, Tokens};
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
    fn test_ssh_option() {
        use std::str::FromStr;

        macro_rules! assert_parse {
            ($s:expr, $opt:expr) => {
                assert_eq!(
                    SSHOption::from_str($s)
                        .expect(format!("parse failed on input {:?}", $s).as_str()),
                    $opt,
                    "for input: {:?}",
                    $s
                );
            };
        }

        assert_parse!(r#"User dusty"#, SSHOption::User(String::from("dusty")));
        assert_parse!(r#"Port 22"#, SSHOption::Port(22));
        // TODO: getservbyname
        // assert_parse!(r#"Port ssh"#, SSHOption::Port(22));
    }

    #[test]
    fn test_parse_tokens() {
        assert_matches!(
            parse_tokens::<_, _, Error>("", |_, _| Ok(())),
            Ok(None),
            "expected to successfully parse nothing"
        );

        for spelling in &[
            r#"Hello World"#,
            r#"=Hello World"#,
            r#"HeLlO World"#,
            r#"HEllo       World"#,
            r#"HEllo  "World""#,
            r#""HEllo"  "World""#,
            r#"H"Ello"  World"#,
            r#"H"Ello"  "World""#,
            r#"HEllo  Wo"rld""#,
            r#""HEllo"  Wo"rld""#,
            r#"HE"llo"  Wo"rld""#,
            r#""Hello"World"#,
            r#""Hello""World""#,
            r#"H"ello""World""#,
            r#"H"ello"W"orld""#,
        ] {
            parse_tokens::<_, _, Error>(spelling, |k, toks| {
                Tokens::with_one_arg(toks, |v| {
                    Ok(assert_eq!(
                        (k, v),
                        ("hello", "World"),
                        "failed for input: {:?}",
                        spelling
                    ))
                })
            })
            .expect(format!("parse failed for input: {:?}", spelling).as_str())
            .expect("nothing found");
        }

        parse_tokens::<_, _, Error>("h\"el lo  \"       wo\" rld\"", |k, toks| {
            Tokens::with_one_arg(toks, |v| Ok(assert_eq!((k, v), ("hel lo  ", "wo rld"))))
        })
        .expect("parse failed")
        .expect("nothing found");

        // TODO: is this one ok?
        parse_tokens::<_, _, Error>("hello=", |k, _| Ok(assert_eq!(k, "hello")))
            .expect("wanted to skip trailing delimiter(s)")
            .expect("nothing found");
    }

    #[test]
    fn test_parse_tokens_err() {
        assert_matches!(
            parse_tokens::<(), _, _>("a b", |_, _| Err(Error::MissingArgument))
                .expect_err("wanted parse error"),
            Error::MissingArgument
        );

        assert_matches!(
            parse_tokens::<_, _, Error>("hello world", |_, _| Ok(()))
                .expect_err("wanted parse error for unconsumed tokens"),
            Error::TrailingGarbage(w) => assert_eq!(w, "world")
        );

        assert_matches!(
            parse_tokens::<_, _, Error>("\"ello", |_, _| Ok(())).expect_err("wanted parse error"),
            Error::UnmatchedQuote(s) => assert_eq!(s, "ello")
        );
        assert_matches!(
            parse_tokens::<_, _, Error>("h\"ello", |_, _| Ok(())).expect_err("wanted parse error"),
            Error::UnmatchedQuote(s) => assert_eq!(s, "ello")
        );
        assert_matches!(
            parse_tokens::<_, _, Error>("h\"\"\"ello", |_, _| Ok(()))
                .expect_err("wanted parse error"),
            Error::UnmatchedQuote(s) => assert_eq!(s, "ello")
        );
        assert_matches!(
            parse_tokens::<_, _, Error>("\"h\"\"ello", |_, _| Ok(()))
                .expect_err("wanted parse error"),
            Error::UnmatchedQuote(s) => assert_eq!(s, "ello")
        );
    }
}
