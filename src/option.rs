#![warn(missing_docs, unused_results)]
#![cfg_attr(test, deny(warnings))]

use core::str::CharIndices;
use std::fmt;
use std::iter::Peekable;
#[allow(unused)]
use std::str::MatchIndices;

/// SSHOption represents a single configuration parameter.
///
/// For details on the individual meaning of these options, see [ssh_config(5)][0].
///
/// [0]: https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5
#[derive(Debug, PartialEq, Eq)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum SSHOption {
    User(String),
    Port(u16),
    Hostname(String),
}

/// parse_opt reads a single option from a single line of config.
///
/// The ssh_config format is entirely line-oriented (no option may span multiple lines), so it's best to use
/// this in coordination with [`str::lines`]. This function returns `Result<Option<_>, _>` as it is possible
/// to successfully parse no option from either a comment or a blank line.
///
/// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
///
/// # Example
///
/// ```
/// use ssh2_config::option::{parse_opt, SSHOption};
///
/// let opts: Result<Vec<_>, _> = r#"# a comment
/// Hostname example.com
/// Port 22
/// "#
///     .lines()
///     .filter_map(|line| parse_opt(line).transpose())
///     .collect();
///
/// assert_eq!(
///     opts.unwrap(),
///     vec![SSHOption::Hostname(String::from("example.com")), SSHOption::Port(22)],
/// );
/// ```
pub fn parse_opt(line: &str) -> Result<Option<SSHOption>, Error> {
    // TODO: it's a context-sensitive grammar for UserKnownHostsFile, GlobalKnownHostsFile, and RekeyLimit.
    use SSHOption::*;
    parse_tokens(line, |keyword, args| match keyword {
        "user" => args.with_one(|arg| Ok(User(arg.to_owned()))),
        "port" => args.with_one(|arg| Ok(Port(arg.parse().map_err(DetailedError::InvalidPort)?))),
        "hostname" => args.with_one(|arg| Ok(Hostname(arg.to_owned()))),
        _ => Err(Error::from(DetailedError::BadOption(keyword.to_string()))),
    })
}

impl std::str::FromStr for SSHOption {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match parse_opt(s).transpose() {
            Some(res) => res,
            None => Err(Error::MissingArgument),
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
/// parse_tokens::<_, _, Error>(r#""OPTION" "Hello There""#, |opt, args| {
///     assert_eq!(opt, "option");
///     args.with_one(|val| {
///         Ok(assert_eq!(val, "Hello There"))
///     })
/// })
/// .expect("parse failed")
/// .expect("nothing found");
/// ```
///
/// `parse_tokens` will also check that either all of the tokens from a line are consumed, or, for
/// compatibility reasons, that the next unconsumed token is empty. Also for compatibility reasons, lines
/// beginning with two empty arguments are considered entirely empty.
///
/// Note that, since all of the known ssh option keywords are exclusively in the ASCII character space,
/// we avoid handling of arbitrary unicode code points in the key portion of the line.
///
/// Note also that there are some unexpected arrangements of tokens that ssh will accept. For more
/// information on these, see [`Arguments`] and [`Token`].
///
/// [`Arguments`]: crate::option::Arguments
/// [`Token`]: crate::option::Token
pub fn parse_tokens<T, F, E>(line: &str, f: F) -> Result<Option<T>, Error>
where
    F: FnOnce(&str, &mut Arguments) -> Result<T, E>,
    Error: From<E>,
{
    let mut args = Arguments::new(tokens(line));
    if !args.has_next() {
        return Ok(None);
    }

    let res = args.with_next(|k, args| {
        // COMPAT: consider a line with two empty keywords to be blank
        if !k.is_empty() {
            Ok(Some(f(&k.to_ascii_lowercase(), args)?))
        } else {
            // Skip one empty keyword, give up after two
            args.with_next(|k, args| {
                if !k.is_empty() {
                    Ok(Some(f(&k.to_ascii_lowercase(), args)?))
                } else {
                    Ok(None)
                }
            })
        }
        // END COMPAT
    })?;

    if res.is_none() {
        return Ok(None);
    }

    match args.0.next() {
        None => Ok(res),
        // COMPAT: allow anything following an "empty" arguments
        Some(Token::Delim) => Ok(res),
        Some(Token::Word(s)) | Some(Token::Quoted(s)) if s.is_empty() => Ok(res),
        // END COMPAT
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
    /// UnsupportedOption occurs when an option was recognized as no longer supported.
    UnsupportedOption(String),
    /// BadOption occurs when we encounter an unknown or misspelled option.
    BadOption(String),

    /// InvalidPort occurs when we encounter a port that can't be recognize, e.g. `Port -1`
    // TODO: getservfromname
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
/// These token streams are not complete, choosing to omit end-of-line blank characters as these have
/// no semantic importance to the format. For more details on the SSH option format, see [`Arguments`]
/// and [`Token`].
///
/// Note: In order to maintain compatibility with some of the more unusual parts of the config language,
/// we interpret the digraph `"=` (closing-quote-equals) as being a blank `Word("")`.
///
/// [`Token`s]: crate::option::Token
/// [`Token`]: crate::option::Token
/// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
/// [`Arguments`]: crate::option::Arguments
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
        line,
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
    /// Ex. `KnownHostsFile` -> Word("KnownHostsFile")
    Word(&'a str),
    /// Ex. `"KnownHostsFile"` -> Quoted("KnownHostsFile")
    Quoted(&'a str),
    /// Repeated blanks, including at most one `=`
    Delim,
    /// Ex. unmatched quote: `"foo` -> `Invalid("foo")`
    Invalid(&'a str),
}

/// Arguments provide access to the configuration statements in a line.
///
/// As with many "found" languages, the SSH config language accepts some unexpected
/// and surprising items: `Port 22` is an accepted way to spell the pair of arguments
/// `("Port", "22")`, but so is `Po"rt"2"2"`:
///
/// ```
/// use ssh2_config::option::{Arguments, tokens};
///
/// Arguments::new(tokens(r#"Port 22"#)).with_next(|port, args| {
///     args.with_one(|num| Ok(assert_eq!((port, num), ("Port", "22"))))
/// });
///
/// Arguments::new(tokens(r#"Po"rt"2"2""#)).with_next(|port, args| {
///     args.with_one(|num| Ok(assert_eq!((port, num), ("Port", "22"))))
/// });
/// ```
///
/// We use closures to provide access to the arguments themselves in order to "pay for
/// what you use" in this regard: the closure always takes a reference to a string, and
/// in the first case where we can return pointers into the original configuration we do
/// so. In the latter, we need to allocate (and/or modify, as upstream SSH does) in
/// order to remove the "interior" quote, but the closure allows us to only do that
/// additional work if the provided config requires it.
///
/// Arguments internally preserves the invariant that the stream does not begin with a
/// "Delim" token, instead greedily consuming one if it exists for the preceding argument.
pub struct Arguments<'a>(itertools::PutBack<Tokens<'a>>);

#[allow(missing_docs)] // TODO
impl<'a> Arguments<'a> {
    /// new constructs a new Arguments wrapper for a stream of `Token`s
    pub fn new(tokens: Tokens<'a>) -> Self {
        Arguments(itertools::put_back(tokens))
    }

    /// has_next returns true if there is at least one more argument.
    pub fn has_next(self: &mut Self) -> bool {
        if let Some(next) = self.0.next() {
            self.0.put_back(next);
            true
        } else {
            false
        }
    }

    pub fn with_one<T, F>(self: &mut Self, f: F) -> Result<T, Error>
    where
        F: FnOnce(&str) -> Result<T, Error>,
    {
        self.with_next(|a, _| f(a))
    }

    // comparable to strdelim
    pub fn with_next<T, F>(self: &mut Self, f: F) -> Result<T, Error>
    where
        F: FnOnce(&str, &mut Self) -> Result<T, Error>,
    {
        use Token::*;

        match self.0.next() {
            None => Err(Error::MissingArgument),
            Some(Word(w)) => match self.0.next() {
                None | Some(Delim) => f(w, self),
                Some(Quoted(q)) => {
                    let arg = format!("{}{}", w, q);
                    match self.0.next() {
                        None | Some(Delim) => f(&arg, self),
                        Some(next @ Word(_)) | Some(next @ Quoted(_)) => {
                            self.0.put_back(next);
                            f(&arg, self)
                        }
                        Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
                    }
                }
                // We can't see back-to-back word tokens
                Some(Word(_)) => unreachable!(),
                Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
            },
            Some(Quoted(w)) => match self.0.next() {
                None | Some(Delim) => f(w, self),
                Some(next @ Quoted(_)) | Some(next @ Word(_)) => {
                    self.0.put_back(next);
                    f(w, self)
                }
                Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
            },
            Some(Delim) => f("", self),
            Some(Invalid(inv)) => Err(Error::UnmatchedQuote(inv.to_owned())),
        }
    }
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
    pub const DELIMITERS: &'static [char] = &[' ', '\t' /* TODO: \r? */];

    /// Blanks are a superset of Delimiters that are considered "ignorable," but only when they appear at
    /// the beginning of a line.
    ///
    /// Note that we differ from [upstream] by omitting the newline `'\n'` character from this set.
    ///
    /// [upstream]: https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L323-L325
    pub const BLANK: &'static [char] = &[' ', '\t', '\r'];

    /// EOL blanks are the set of characters that are "ignorable" at the end of a line.
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
            // Comments are only valid at the beginning of the line (except for leading blanks)
            // See: https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L932
            (0, '#') => {
                self.chars = "".char_indices().peekable();
                None
            }
            (i, ch) if Tokens::DELIMITERS.contains(ch) || *ch == '=' => {
                // Only blanks are "delimiters" after a `"`
                let mut eq = *i > '"'.len_utf8()
                    && &self.line.as_bytes()[i - '"'.len_utf8()..*i] == "\"".as_bytes();
                if *ch == '=' && eq {
                    // "= digraph
                    let _ = self.chars.next();
                    return Some(Token::Word(""));
                }
                while let Some((_, ch)) = self.chars.peek() {
                    if !Tokens::DELIMITERS.contains(ch) && (*ch != '=' || eq) {
                        break;
                    }
                    eq = eq || *ch == '=';
                    let _ = self.chars.next();
                }
                Some(Token::Delim)
            }
            (start, '"') => {
                let start = start + '"'.len_utf8();
                let _ = self.chars.next();
                while let Some((_, ch)) = self.chars.peek() {
                    if *ch == '"' || *ch == '\n' {
                        break;
                    }
                    let _ = self.chars.next();
                }
                if let Some((end, ch)) = self.chars.next() {
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
                    if Tokens::DELIMITERS.contains(ch) || *ch == '"' || *ch == '=' {
                        end = *i;
                        break;
                    }
                    let _ = self.chars.next();
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
    use super::{parse_tokens, tokens, Error};
    use itertools::Itertools;

    #[test]
    fn test_tokens() {
        macro_rules! case {
            {input: $left:expr, expect: $right:expr} => ({
                case!($left, $right, None)
            });
            {input: $left:expr, expect: $right:expr,} => ({
                case!($left, $right, None)
            });
            {input: $left:expr, expect: $right:expr, message: $msg:expr} => ({
                case!($left, $right, Some($msg))
            });
            {input: $left:expr, expect: $right:expr, message: $msg:expr,} => ({
                case!($left, $right, Some($msg))
            });
            ($input:expr, $expect:expr, $msg:expr) => ({
                match ($input, $expect, $msg) {
                    (input, expect, message) => {
                        let mut out = tokens(input);
                        let actual = out.by_ref().take(expect.len() + 1).collect::<Vec<_>>();
                        let more = out.next().is_some();
                        assert!(
                            actual == expect && !more,
                            r#"assertion failed: `tokens({:?}) == expected`
              actual: `[{:?}{}]`,
            expected: `{:?}`{}"#,
                            input,
                            actual.iter().format(", "),
                            if more { ", .." } else { "" },
                            expect,
                            message
                                .map(|e: &str| format!(": {}", e))
                                .unwrap_or("".to_string()),
                        );
                    }
                }
            });
        }

        case! {
            input: "",
            expect: vec![],
        };
        case! {
            input: "key",
            expect: vec![Word("key")],
        };
        case! {
            input: "key val",
            expect: vec![Word("key"), Delim, Word("val")],
        };
        case! {
            input: "key=val",
            expect: vec![Word("key"), Delim, Word("val")],
        };
        case! {
            input: "key==val",
            expect: vec![Word("key"), Delim, Delim, Word("val")],
        };
        case! {
            input: "key=      =val",
            expect: vec![Word("key"), Delim, Delim, Word("val")],
        };
        case! {
            input: "=key val",
            expect: vec![Delim, Word("key"), Delim, Word("val")],
            message: "tokens should not omit leading delimiters",
        };
        case! {
            input: "key val\t\r\x0c",
            expect: vec![Word("key"), Delim, Word("val")],
            message: "tokens should omit trailing blanks",
        };
        case! {
            input: "key val=",
            expect: vec![Word("key"), Delim, Word("val"), Delim],
            message: "tokens should preserve trailing `=`s",
        };
        case! {
            input: "key \"val\"",
            expect: vec![Word("key"), Delim, Quoted("val")],
        };
        case! {
            input: "w1\"w2\"",
            expect: vec![Word("w1"), Quoted("w2")],
        };
        case! {
            input: "\"w1",
            expect: vec![Invalid("w1")],
        };
        case! {
            input: "\"\"",
            expect: vec![Quoted("")],
        };
        // These two corner cases are unfortunate
        case! {
            input: "\"key\" =val",
            expect: vec![Quoted("key"), Delim, Delim, Word("val")],
            message: "quotes don't greedily consume following =, only blanks",
        };
        case! {
            input: "\"key\"=val",
            expect: vec![Quoted("key"), Word(""), Word("val")],
            message: "we invent a zero-width Word for the digraph \"=`",
        };
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
        assert_matches!(
            parse_tokens::<_, _, Error>("", |_, _| Ok(())),
            Ok(None),
            "expected to successfully parse nothing"
        );
        assert_matches!(
            parse_tokens::<_, _, Error>("# comment", |_, _| Ok(())),
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
            parse_tokens::<_, _, Error>(spelling, |k, args| {
                args.with_one(|v| {
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

        parse_tokens::<_, _, Error>("h\"el lo  \"       wo\" rld\"", |k, args| {
            args.with_one(|v| Ok(assert_eq!((k, v), ("hel lo  ", "wo rld"))))
        })
        .expect("parse failed")
        .expect("nothing found");

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
            parse_tokens::<_, _, Error>("key #comment", |_, _| Ok(())).expect_err("wanted parse error"),
            Error::TrailingGarbage(w) => assert_eq!(w, "#comment")
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
}
