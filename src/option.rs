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
    parse_tokens(line, |keyword, args| {
        std::convert::TryFrom::try_from((keyword, args))
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

impl<A> std::convert::TryFrom<(&str, &mut A)> for SSHOption
where
    A: Arguments,
{
    type Error = Error;

    fn try_from((keyword, args): (&str, &mut A)) -> Result<Self, Self::Error> {
        // TODO: it's a context-sensitive grammar for UserKnownHostsFile, GlobalKnownHostsFile, and RekeyLimit.
        use SSHOption::*;

        match keyword.to_ascii_lowercase().as_str() {
            "user" => args.map_owned(User),
            "port" => args.map_next(|arg, _| Ok(Port(a2port(arg)?))),
            "hostname" => args.map_owned(Hostname),

            _ => Err(Error::from(DetailedError::BadOption(keyword.to_string()))),
        }
    }
}

#[cfg(not(feature = "with_libc"))]
fn a2port(s: &str) -> Result<u16, std::num::ParseIntError> {
    s.parse()
}

// See: https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L414-L432
#[cfg(feature = "with_libc")]
fn a2port(s: &str) -> Result<u16, std::num::ParseIntError> {
    use libc::getservbyname;
    use std::convert::TryInto;
    use std::ffi::CString;

    match s.parse() {
        res @ Ok(_) => res,
        num_err @ Err(_) => match CString::new(s) {
            Ok(cstr) => unsafe {
                let servent = getservbyname(
                    cstr.as_ptr(),
                    CString::new("tcp").expect("CString::new failed").as_ptr(),
                );
                if servent.is_null() {
                    num_err
                } else {
                    // network byte order is big-endian
                    Ok(u16::from_be((*servent).s_port.try_into().expect(
                        "`/etc/services` database entry for port out of range (<0 or >65,536)",
                    )))
                }
            },
            Err(_) => num_err,
        },
    }
}

/// Accepts a line and calls the provided closure with exactly one tokenized option.
///
/// It normalizes the tokens into single argument form by handling quoted segments:
///
/// ```
/// use ssh2_config::option::{Arguments, Error, parse_tokens, Token, Tokens};
///
/// parse_tokens::<_, _, Error>(r#""option" "Hello There""#, |opt, args| {
///     assert_eq!(opt, "option");
///     args.map_next(|val, _| {
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
/// information on these, see [`Args`] and [`Token`].
///
/// [`Args`]: crate::option::Args
/// [`Token`]: crate::option::Token
pub fn parse_tokens<T, F, E>(line: &str, f: F) -> Result<Option<T>, Error>
where
    F: FnOnce(&str, &mut Args) -> Result<T, E>,
    Error: From<E>,
{
    let mut args = Args::new(tokens(line));
    if !args.has_next() {
        return Ok(None);
    }

    let res = args.map_next(|k, args| {
        // COMPAT: consider a line with two empty keywords to be blank
        if !k.is_empty() {
            Ok(Some(f(&k, args)?))
        } else {
            // Skip one empty keyword, give up after two
            args.map_next(|k, args| {
                if !k.is_empty() {
                    Ok(Some(f(&k, args)?))
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
    InvalidPort(std::num::ParseIntError),
}

impl From<std::num::ParseIntError> for Error {
    fn from(e: std::num::ParseIntError) -> Self {
        DetailedError::InvalidPort(e).into()
    }
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
/// no semantic importance to the format. For more details on the SSH option format, see [`Args`]
/// and [`Token`].
///
/// Note: In order to maintain compatibility with some of the more unusual parts of the config language,
/// we interpret the digraph `"=` (closing-quote-equals) as being a blank `Word("")`.
///
/// [`Token`s]: crate::option::Token
/// [`Token`]: crate::option::Token
/// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
/// [`Args`]: crate::option::Args
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

/// Args provide access to the configuration statements in a line.
///
/// As with many "found" languages, the SSH config language accepts some unexpected
/// and surprising items: `Port 22` is an accepted way to spell the pair of arguments
/// `("Port", "22")`, but so is `Po"rt"2"2"`:
///
/// ```
/// use ssh2_config::option::{Args, Arguments, tokens};
///
/// Args::new(tokens(r#"Port 22"#)).map_next(|port, args| {
///     args.map_next(|num, _| Ok(assert_eq!((port, num), ("Port", "22"))))
/// });
///
/// Args::new(tokens(r#"Po"rt"2"2""#)).map_next(|port, args| {
///     args.map_next(|num, _| Ok(assert_eq!((port, num), ("Port", "22"))))
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
pub struct Args<'a>(itertools::PutBack<Tokens<'a>>);

impl<'a> Args<'a> {
    /// new constructs a new Args wrapper for a stream of `Token`s
    pub fn new(tokens: Tokens<'a>) -> Self {
        Args(itertools::put_back(tokens))
    }

    /// has_next returns true if there is at least one more argument.
    fn has_next(self: &mut Self) -> bool {
        if let Some(next) = self.0.next() {
            self.0.put_back(next);
            true
        } else {
            false
        }
    }
}

impl<'a> Iterator for Args<'a> {
    type Item = Result<String, Error>;

    fn next(self: &mut Self) -> Option<Self::Item> {
        match self.map_owned(std::convert::identity) {
            Err(Error::MissingArgument) => None,
            res => Some(res),
        }
    }
}

impl<'a> Arguments for Args<'a> {
    // comparable to strdelim
    fn map_next<T, F>(self: &mut Self, f: F) -> Result<T, Error>
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

/// Arguments represents access to the configuration arguments in a line.
///
/// Implementations should return `Err(MissingArgument)` if `map_next` is called
/// on an empty argument list.
///
/// See:
/// - `SSHOption.try_from((&str, &mut Arguments))`
/// - `Args`
pub trait Arguments: IntoIterator<Item = Result<String, Error>> {
    /// map_next provides access to the next argument and subsequent arguments
    fn map_next<T, F>(self: &mut Self, f: F) -> Result<T, Error>
    where
        F: FnOnce(&str, &mut Self) -> Result<T, Error>;

    /// map_one provides access to a owned copy of the next argument
    fn map_owned<T, F>(self: &mut Self, f: F) -> Result<T, Error>
    where
        F: FnOnce(String) -> T,
    {
        self.map_next(|a, _| Ok(f(a.to_owned())))
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
                let mut eq =
                    *i > '"'.len_utf8() && &self.line.as_bytes()[i - '"'.len_utf8()..*i] == b"\"";
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
    use super::{parse_tokens, tokens, Arguments, Error};
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
            r#"Hello World"#,
            r#"Hello       World"#,
            r#"Hello  "World""#,
            r#""Hello"  "World""#,
            r#"H"ello"  World"#,
            r#"H"ello"  "World""#,
            r#"Hello  Wo"rld""#,
            r#""Hello"  Wo"rld""#,
            r#"He"llo"  Wo"rld""#,
            r#""Hello"World"#,
            r#""Hello""World""#,
            r#"H"ello""World""#,
            r#"H"ello"W"orld""#,
        ] {
            parse_tokens::<_, _, Error>(spelling, |k, args| {
                args.map_next(|v, _| {
                    Ok(assert_eq!(
                        (k, v),
                        ("Hello", "World"),
                        "failed for input: {:?}",
                        spelling
                    ))
                })
            })
            .expect(format!("parse failed for input: {:?}", spelling).as_str())
            .expect("nothing found");
        }

        parse_tokens::<_, _, Error>("h\"el lo  \"       wo\" rld\"", |k, args| {
            args.map_next(|v, _| Ok(assert_eq!((k, v), ("hel lo  ", "wo rld"))))
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
                assert_eq!(SSHOption::from_str($s).expect("parse failed"), $opt);
                assert_eq!(
                    super::simple::parse_opt($s)
                        .expect("parse failed (simple)")
                        .expect("nothing found"),
                    $opt
                );
            };
        }

        assert_parse!(r#"User dusty"#, SSHOption::User(String::from("dusty")));
        assert_parse!(r#"Port 22"#, SSHOption::Port(22));
        if cfg!(feature = "with_libc") {
            assert_parse!(r#"Port ssh"#, SSHOption::Port(22));
        }
    }
}

/// the simple module provides a simplified `ssh_config(5)` language that is expected to cover almost
/// all real-word configuration.
///
/// The grammar for the simplified language is as follows:
///
/// ```ebnf
/// config : line + ;
/// line : blank * [ comment | [ key [ blank + arg | blank * quoted ] + 32 ] ] blank * '\r' ? '\n' ;
/// comment: '#' NON_EOL *
/// key : ASCII_ALPHA + ;
/// quoted : '"' NON_QUOTE * '"' ;
/// blank : ' ' | '\t' | '=' ;
/// arg : [ NON_BLANK | NON_QUOTE ] + ;
/// ```
///
/// where:
///  * NON_EOL is any character other than `\n`
///  * ASCII_ALPHA is any character in the English ASCII alphabet range: [a-zA-Z]
///  * NON_QUOTE is any character besides `"`
///  * NON_BLANK is any character besides `blank`
pub mod simple {
    pub use super::{Arguments, Error, SSHOption};
    use core::str::CharIndices;
    use std::convert::TryFrom;
    use std::iter::Peekable;

    /// parse_opt reads a single option from a single line of config.
    ///
    /// The ssh_config format is entirely line-oriented (no option may span multiple lines), so it's best to use
    /// this in coordination with [`str::lines`]. This function returns `Result<Option<_>, _>` as it is possible
    /// to successfully parse no option from either a comment or a blank line.
    ///
    /// Note: This implementation technically accepts a subset of the configurations that ssh itself will
    /// understand, but should work for almost all configs that are likely to be encountered. For more detail
    /// on what this omits, see the [`simple` module] and [`super::Args`].
    ///
    /// [`simple` module]: crate::options::simple
    /// [`super::Args`]: super::Args
    /// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
    ///
    /// # Example
    ///
    /// ```
    /// use ssh2_config::option::simple::{parse_opt, SSHOption};
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
        let mut args = Args(tokens(line));
        let res = match args.0.next() {
            None => Ok(None),
            Some(keyword) => Some(TryFrom::try_from((keyword?, &mut args))).transpose(),
        };

        match args.0.next() {
            None => res,
            Some(more) => Err(Error::TrailingGarbage(more?.to_owned())),
        }
    }

    struct Args<'a>(Tokens<'a>);

    impl<'a> Iterator for Args<'a> {
        type Item = Result<String, Error>;

        fn next(self: &mut Self) -> Option<Self::Item> {
            Some(self.0.next()?.map(str::to_owned))
        }
    }

    impl<'a> Arguments for Args<'a> {
        fn map_next<T, F>(self: &mut Self, f: F) -> Result<T, Error>
        where
            F: FnOnce(&str, &mut Self) -> Result<T, Error>,
        {
            match self.0.next() {
                None => Err(Error::MissingArgument),
                Some(arg) => f(arg?, self),
            }
        }
    }

    /// An iterator of [`&str`]s created with the method [`tokens`].
    ///
    /// [`tokens`]: crate::option::simple::tokens
    pub struct Tokens<'a> {
        line: &'a str,
        chars: Peekable<CharIndices<'a>>,
    }

    impl<'a> Tokens<'a> {
        const BLANK: &'static [char] = &[' ', '\t', '='];

        fn peeking_find<P>(&mut self, predicate: P) -> Option<&(usize, char)>
        where
            P: Fn(&(usize, char)) -> bool,
        {
            while let Some(e) = self.chars.peek() {
                if predicate(e) {
                    break;
                }
                let _ = self.chars.next();
            }
            self.chars.peek()
        }
    }

    /// `tokens` converts a string into an iterator of [`&str`s], intended for use with [`str::lines`].
    ///
    /// Note that it does not handle carriage return (`\r`) or new
    ///
    /// [`str::lines`]: https://doc.rust-lang.org/std/primitive.str.html#method.lines
    ///
    /// # Example
    ///
    /// ```
    /// use ssh2_config::option::simple;
    /// use ssh2_config::option::simple::Error;
    ///
    /// assert_eq!(
    ///     "hello\nworld"
    ///         .lines()
    ///         .flat_map(simple::tokens)
    ///         .collect::<Result<Vec<_>, Error>>()
    ///         .unwrap(),
    ///     vec!["hello", "world"]
    /// );
    /// ```
    pub fn tokens(line: &str) -> Tokens {
        let line = line
            .trim_start_matches(Tokens::BLANK)
            .trim_end_matches(Tokens::BLANK);
        Tokens {
            line,
            chars: line.char_indices().peekable(),
        }
    }

    impl<'a> Iterator for Tokens<'a> {
        type Item = Result<&'a str, Error>;

        fn next(&mut self) -> Option<Self::Item> {
            match self.chars.next()? {
                // Comments are only valid at the beginning of the line (except for leading blanks)
                // See: https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L932
                (0, '#') => {
                    self.chars = "".char_indices().peekable();
                    None
                }
                (start, '"') => {
                    let start = start + '"'.len_utf8();
                    if let Some((end, ch)) = self.chars.find(|(_, ch)| ch == &'"' || ch == &'\n') {
                        let tok = &self.line[start..end];
                        Some(if ch == '"' {
                            Ok(tok)
                        } else {
                            Err(Error::UnmatchedQuote(tok.to_owned()))
                        })
                    } else {
                        Some(Err(Error::UnmatchedQuote(self.line[start..].to_owned())))
                    }
                }
                (start, _) => {
                    let end = self
                        .peeking_find(|(_, ch)| Tokens::BLANK.contains(ch) || ch == &'"')
                        .map(|&(idx, _)| idx)
                        .unwrap_or_else(|| self.line.len());

                    let _ = self.peeking_find(|(_, ch)| !Tokens::BLANK.contains(ch) || ch == &'"');

                    Some(Ok(&self.line[start..end]))
                }
            }
        }
    }

    #[cfg(test)]
    mod test {
        use super::tokens;
        use itertools::Itertools;

        #[test]
        fn test_tokens() {
            macro_rules! case {
                ({input: $left:expr, expect: $right:expr}) => {{
                    case!($left, $right, None)
                }};
                ({input: $left:expr, expect: $right:expr,}) => {{
                    case!($left, $right, None)
                }};
                ({input: $left:expr, expect: $right:expr, message: $msg:expr}) => {{
                    case!($left, $right, Some($msg))
                }};
                ({input: $left:expr, expect: $right:expr, message: $msg:expr,}) => {{
                    case!($left, $right, Some($msg))
                }};
                ($input:expr, $expect:expr, $msg:expr) => {{
                    let (input, expect, message): (_, Vec<&str>, _) = ($input, $expect, $msg);
                    let mut out = tokens(input);
                    let actual = out
                        .by_ref()
                        .take(expect.len() + 1)
                        .collect::<Result<Vec<_>, _>>()
                        .expect("got invalid token");
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
                }};
            }

            case! ({
                input: "",
                expect: vec![],
            });
            case! ({
                input: "# comment",
                expect: vec![],
            });
            case! ({
                input: "key",
                expect: vec!["key"],
            });
            case! ({
                input: "key val",
                expect: vec!["key", "val"],
            });
            case! ({
                input: "key\tval",
                expect: vec!["key", "val"],
            });
            case! ({
                input: "key \t val",
                expect: vec!["key", "val"],
            });
            case! ({
                input: "key=val",
                expect: vec!["key", "val"],
            });
            case! ({
                input: "key==val",
                expect: vec!["key", "val"],
                message: "the simplified language considers `=` equivalent to any other blank",
            });
            case! ({
                input: "     key=      =val   ",
                expect: vec!["key", "val"],
                message: "both leading and trailing blanks should be stripped",
            });
            case! ({
                input: "key \"val\"",
                expect: vec!["key", "val"],
            });
            case! ({
                input: "key\"val1\"val2",
                expect: vec!["key", "val1", "val2"],
                message: "the simplified language breaks on quotes",
            });
            case! ({
                input: "key\"\"val",
                expect: vec!["key", "", "val"],
                message: "the simplified language breaks on quotes",
            });
        }
    }
}
