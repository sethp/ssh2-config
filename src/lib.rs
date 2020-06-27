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
// #![cfg_attr(test, deny(warnings))]

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
pub enum SSHOption {
    User(String),
    Port(u16),

    // Most things, right now
    Unknown(String, String),
}

// TODO: line + file info?
#[derive(Debug)]
pub enum Error {
    TrailingGarbage(String),

    InvalidPort(std::num::ParseIntError),
}

use std::error;
use std::fmt;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::TrailingGarbage(ref garbage) => write!(f, "garbage at end of line: {}", garbage),

            Error::InvalidPort(ref err) => write!(f, "invalid port: {}", err),
        }
    }
}

impl error::Error for Error {}

type Result<T> = std::result::Result<T, Error>;

impl SSHOption {
    pub fn parse(s: String) -> Result<Option<SSHOption>> {
        match parse_line(s)? {
            None => Ok(None),
            Some(v) => do_the_inner_thing(v).map(Option::from),
        }
    }
}

fn do_the_inner_thing(opt: (String, String)) -> Result<SSHOption> {
    use SSHOption::*;
    match opt.0.as_str() {
        "user" => Ok(User(opt.1)),
        "port" => Ok(Port(opt.1.parse().map_err(Error::InvalidPort)?)), // TODO: getservbyname
        _ => Ok(Unknown(opt.0, opt.1)),
    }
}

// The rule is that we can accept ssh configs openssh won't (even invalid or broken ones),
// but we can't reject any that it would accept.
// https://github.com/openssh/openssh-portable/blob/14beca57ac92d62830c42444c26ba861812dc837/readconf.c#L892
fn parse_line(s: String) -> Result<Option<(String, String)>> {
    let s = s.trim_start_matches(WHITESPACE);
    if s.starts_with("#") {
        return Ok(None);
    }
    let s = s.trim_end_matches(EOL_WHITESPACE);

    // This might allow more than one = delimiter
    let parts = s.splitn(3, WHITESPACE).collect::<Vec<_>>();

    match parts.as_slice() {
        [] => Ok(None),
        [keyword, value] => Ok(Some((
            keyword.to_lowercase().to_string(),
            value.to_string(),
        ))),
        [.., garbage] => Err(Error::TrailingGarbage(garbage.to_string())),
    }
}

// https://github.com/openssh/openssh-portable/blob/e073106f370cdd2679e41f6f55a37b491f0e82fe/misc.c#L323-L325
const WHITESPACE: &[char] = &[' ', '=', '\t', '\r', '\n'];
// TODO
// const QUOTE: &[char] = &['"'];

const EOL_WHITESPACE: &[char] = &[' ', '\t', '\r', '\n', '\x0c' /* form feed */];

#[test]
fn it_works() {
    assert_eq!(
        parse_line("=# some comment\r\n".to_string()).expect("parse failed"),
        None
    );

    assert_eq!(
        parse_line("user seth".to_string())
            .expect("parse failed")
            .expect("expected value"),
        ("user".to_string(), "seth".to_string())
    );
    assert_eq!(
        parse_line("user seth\r\n".to_string())
            .expect("parse failed")
            .expect("expected value"),
        ("user".to_string(), "seth".to_string())
    );
    assert_eq!(
        format!(
            "{}",
            parse_line("user seth zzz\r\n".to_string()).expect_err("parse should have failed")
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
            SSHOption::parse("user dusty".to_owned())
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::User("dusty".to_owned())
        )
    }

    #[test]
    fn it_works2() {
        assert_eq!(
            SSHOption::parse("port 22".to_owned())
                .expect("parse failed")
                .expect("expected value"),
            SSHOption::Port(22)
        );

        SSHOption::parse("port 222222".to_owned()).expect_err("parse should have failed");
        SSHOption::parse("port zz".to_owned()).expect_err("parse should have failed");
    }
}
