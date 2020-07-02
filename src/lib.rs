//! ```no_run
//! use ssh2::Session;
//! use ssh2_config::SSHConfig;
//!
//! // Connect to the local SSH server
//! let sess = SSHConfig::for_host("127.0.0.1")
//!                 .with_config_file("/path/to/ssh/config") // equivalent to OpenSSH's `-F`
//!                 .connect_with_auth();
//!
//! // Make sure we're authenticated
//! assert!(sess.authenticated());
//! ```

// TODO
// #![doc(html_root_url = "https://docs.rs/ssh2-config")]
// #![deny(missing_docs, unused_results)]
#![cfg_attr(test, deny(warnings))]

// https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5

pub struct SSHConfig {}

impl SSHConfig {
    pub fn for_host(_: &str) -> SSHConfig {
        unimplemented!()
    }

    pub fn with_config_file(self: &Self, _: &str) -> SSHConfig {
        unimplemented!()
    }

    pub fn connect_with_auth(self: &Self) -> ssh2::Session {
        unimplemented!()
    }
}

#[cfg_attr(test, derive(PartialEq, Eq, Debug))]
pub enum SSHOption<'a> {
    User(&'a str),
    Port(u16),

    // Most things, right now
    Unknown(String, &'a str),
}

// TODO: line + file info?
#[derive(Debug)]
pub enum Error<'a> {
    UnmatchedQuote,
    TrailingGarbage(&'a str),

    InvalidPort(std::num::ParseIntError),
}

use std::error;
use std::fmt;

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnmatchedQuote => write!(f, "no matching `\"` found"),
            Error::TrailingGarbage(ref garbage) => write!(f, "garbage at end of line: {}", garbage),

            Error::InvalidPort(ref err) => write!(f, "invalid port: {}", err),
        }
    }
}

impl<'a> error::Error for Error<'a> {}

type Result<'a, T> = std::result::Result<T, Error<'a>>;

impl<'a> SSHOption<'a> {
    pub fn parse(s: &'a str) -> Result<'a, Option<SSHOption<'a>>> {
        parse_line(&s)
    }
}

fn do_the_inner_thing<'a, 'b>(keyword: &'b str, opt: &'a str) -> Result<'a, SSHOption<'a>> {
    use SSHOption::*;
    match keyword {
        "user" => Ok(User(opt)),
        "port" => Ok(Port(opt.parse().map_err(Error::InvalidPort)?)), // TODO: getservbyname
        _ => Ok(Unknown(keyword.to_owned(), opt)),
    }
}

// The rule is that we can accept ssh configs openssh won't (even invalid or broken ones),
// but we can't reject any that it would accept.
// https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L892
fn parse_line<'a>(s: &'a str) -> Result<'_, Option<SSHOption<'a>>> {
    let mut is_quoted = false;
    // TODO: how to deal with an internal `"`, as in foo" bar" (should parse to -> `foo bar`)
    // Seems to require either:
    // 1. Taking in a String so we can mutate it to elide the inner " like readconf.c does
    //    - Pro: It's unlikely that anyone else wants to hold on to a reference to the string we're parsing
    //    - Con: More awkward to use, requires lots of `to_string()`
    //    - ??: `SSHOption`s need to own their string argument(s), but
    //    - ??: Maybe we have to ^ anyway when it comes time to set options in c-land?
    // 2. Allocating a new String copy with the inner " elided
    //    - Pro: No mutation? Closer to the way readconf.c does it?
    //    - Con: don't think there's a way to do the allocation _only_ if there's an inner quote (else a &str works)...
    //           maybe if we're part of a larger whole that can optionally own things and we can assign ownership to
    //           (optional ownership is what, a vec? should options optionally own things? what's the cost of an empty vec?)
    //    - ??: `SSHOption`s need to own their string argument(s), but
    //    - ??: Maybe we have to ^ anyway when it comes time to set options in c-land?
    let parts = s
        .trim_start_matches(WHITESPACE)
        .trim_end_matches(EOL_WHITESPACE)
        // TODO: sure would be nice to recover the bounded `splitn` semantic
        // This will allow more than one = delimiter
        .split(|ch: char| -> bool {
            if ch == QUOTE {
                is_quoted = !is_quoted;
                true
            } else if is_quoted {
                false
            } else {
                WHITESPACE.contains(&ch)
            }
        })
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();

    match parts.as_slice() {
        [..] if is_quoted => Err(Error::UnmatchedQuote),
        [] => Ok(None),
        [word, ..] if word.starts_with('#') => Ok(None),
        [keyword, value] => Ok(Some(do_the_inner_thing(&keyword.to_lowercase(), value)?)),
        [.., garbage] => Err(Error::TrailingGarbage(garbage)),
    }
}

// https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L323-L325
const WHITESPACE: &[char] = &[
    ' ', '\t', '\r', '\n', /* for convenience, treat as blank */ '=',
];
const QUOTE: char = '"';

const EOL_WHITESPACE: &[char] = &[' ', '\t', '\r', '\n', '\x0c' /* form feed */];

#[test]
fn it_works() {
    use SSHOption::*;
    assert_eq!(parse_line("\r\n").expect("parse failed"), None);
    assert_eq!(
        parse_line("=# some comment\r\n").expect("parse failed"),
        None
    );

    assert_eq!(
        parse_line("user seth")
            .expect("parse failed")
            .expect("expected value"),
        User("seth")
    );
    assert_eq!(
        parse_line("user seth\r\n")
            .expect("parse failed")
            .expect("expected value"),
        User("seth")
    );
    assert_eq!(
        parse_line("\"user\" seth")
            .expect("parse failed")
            .expect("expected value"),
        User("seth")
    );
    assert_eq!(
        parse_line("\"user\" \"seth\"")
            .expect("parse failed")
            .expect("expected value"),
        User("seth")
    );
    assert_eq!(
        format!(
            "{}",
            parse_line("user seth zzz\r\n").expect_err("parse should have failed")
        ),
        "garbage at end of line: zzz"
    );
}

#[cfg(test)]
mod tests {
    use crate::SSHOption;

    #[test]
    fn it_works() {
        assert_eq!(
            SSHOption::parse("user dusty")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::User("dusty")
        )
    }

    #[test]
    fn it_works2() {
        assert_eq!(
            SSHOption::parse("port 22")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::Port(22)
        );
        assert_eq!(
            SSHOption::parse("port  22")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::Port(22)
        );

        SSHOption::parse("port 222222").expect_err("parse should have failed");
        SSHOption::parse("port zz").expect_err("parse should have failed");
    }

    #[test]
    fn simple_quoted_tokens() {
        assert_eq!(
            SSHOption::parse("port \"22\"")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::Port(22)
        );
        assert_eq!(
            SSHOption::parse("user \"one two\"")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::User("one two")
        );
        SSHOption::parse("user \"hi").expect_err("parse should have failed");
    }

    #[test]
    #[ignore] // TODO handle internal "
    fn inner_quoted_tokens() {
        assert_eq!(
            SSHOption::parse("port 2\"2\"")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::Port(22)
        );
        assert_eq!(
            SSHOption::parse("user one\" two\"")
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::User("one two")
        );

        SSHOption::parse("user one\" \"two").expect_err("parse should have failed");
    }
}
