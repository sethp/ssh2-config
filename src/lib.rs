//! ```no_run
//! use ssh2::Session;
//! use ssh2_config::SSHConfig;
//!
//! // Retrieve config for local SSH server
//! let sess = SSHConfig::for_host("127.0.0.1")
//!                 .with_config_file("/path/to/ssh/config") // equivalent to OpenSSH's `-F`
//!                 .connect_with_auth();
//!
//! // Make sure we're authenticated
//! assert!(sess.authenticated());
//! ```

// TODO
// #![doc(html_root_url = "https://docs.rs/ssh2-config")]
#![deny(missing_docs, unused_results)]
#![cfg_attr(test, deny(warnings))]

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

/// Individual SSH config options, e.g. `Port 22` or `Hostname example.com`
pub mod option;

pub use option::SSHOption;

use std::fmt;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

#[allow(missing_docs)]
// https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5
pub struct SSHConfig(pub Vec<option::SSHOption>);

// #[allow(missing_docs)]
// pub struct SSHConfig {
//     config: Vec<option::SSHOption>,
// }

impl std::default::Default for SSHConfig {
    fn default() -> Self {
        use SSHOption::*;
        SSHConfig(vec![Port(22)])
    }
}

#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    Read(io::Error),
    Parse(option::Error),
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            Error::Read(ref err) => Some(err),
            Error::Parse(ref err) => Some(err),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Read(ref err) => write!(f, "error reading config file: {}", err),
            Error::Parse(ref err) => write!(f, "config error: {}", err),
        }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::Read(e)
    }
}

impl From<option::Error> for Error {
    fn from(e: option::Error) -> Self {
        Error::Parse(e)
    }
}

#[allow(missing_docs)]
impl SSHConfig {
    pub fn from_default_files() -> Result<SSHConfig, Error> {
        // TODO: https://github.com/openssh/openssh-portable/blob/25e3bccbaa63d27b9d5e09c123f1eb28594d2bd6/ssh.c#L545
        // getpwuid
        Ok(SSHConfig(
            // TODO /etc/ssh/ssh_config
            read_lines(
                &[&std::env::var("HOME").unwrap(), ".ssh", "config"]
                    .iter()
                    .collect::<PathBuf>()
                    .as_path(),
            )?
            .chain(read_lines(
                &["/etc", "ssh", "ssh_config"]
                    .iter()
                    .collect::<PathBuf>()
                    .as_path(),
            )?)
            .filter_map(|line| line.and_then2::<Error>(option::parse_opt).transpose())
            .collect::<Result<_, _>>()?,
        ))
    }

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

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

trait ErrLattice<T, U, F, E1, E2>
where
    F: FnOnce(T) -> Result<U, E2>,
{
    fn and_then2<E>(self, op: F) -> Result<U, E>
    where
        E: From<E1> + From<E2>;
}

impl<T, U, F, E1, E2> ErrLattice<T, U, F, E1, E2> for Result<T, E1>
where
    F: FnOnce(T) -> Result<U, E2>,
{
    fn and_then2<E>(self, op: F) -> Result<U, E>
    where
        E: From<E1> + From<E2>,
    {
        match self {
            Ok(t) => op(t).map_err(From::from),
            Err(e) => Err(From::from(e)),
        }
    }
}

#[test]
fn it_works() {
    let cfg = SSHConfig::from_default_files().expect("read failed");
    assert_eq!(
        cfg.0,
        vec![
            SSHOption::Host(String::from("github.com")),
            SSHOption::User(String::from("git")),
            SSHOption::Host(String::from("bitbucket.org")),
            SSHOption::User(String::from("git")),
            SSHOption::Host(String::from("*")),
            SSHOption::SendEnv(vec![
                option::Env::Send(String::from("LANG")),
                option::Env::Send(String::from("LC_*"))
            ]),
        ]
    )
}
