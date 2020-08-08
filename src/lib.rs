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

#[cfg(feature = "with_libc")]
extern crate libc;

/// Individual SSH config options, e.g. `Port 22` or `Hostname example.com`
pub mod option;

pub use option::SSHOption;

use std::fmt;
use std::fs::{self, File};
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

#[allow(missing_docs)]
#[derive(Debug)]
// https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5
pub struct SSHConfig(pub Vec<option::SSHOption>);

// #[allow(missing_docs)]
// pub struct SSHConfig {
//     config: Vec<option::SSHOption>,
// }

impl std::default::Default for SSHConfig {
    fn default() -> Self {
        use SSHOption::*;
        SSHConfig(vec![
            Host("*".to_owned()),
            Port(option::a2port("ssh").unwrap_or(22)),
        ])
    }
}

#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    Read(io::Error),
    Parse(option::Error),
    MaxDepthExceeded,
    PermissionError,
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            Error::Read(ref err) => Some(err),
            Error::Parse(ref err) => Some(err),
            _ => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Read(ref err) => write!(f, "error reading config file: {}", err),
            Error::Parse(ref err) => write!(f, "config error: {}", err),
            Error::MaxDepthExceeded => write!(
                f,
                "exceeded maximum depth while processing include, max: {}",
                MAX_READCONF_DEPTH
            ),
            Error::PermissionError => {
                write!(f, "Bad owner or permissions (writable by group or world)")
            }
        }
    }
}

/// MAX_READCONF_DEPTH is the maximum depth level of config file we will process
///
/// Note that the first file we process is considered to be at depth 0, so we'll process
/// MAX_READCONF_DEPTH + 1 `Include` directives before bailing.
pub const MAX_READCONF_DEPTH: usize = 16;

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
    pub fn from_default_files() -> Result<Self, Error> {
        // TODO: https://github.com/openssh/openssh-portable/blob/25e3bccbaa63d27b9d5e09c123f1eb28594d2bd6/ssh.c#L545
        // getpwuid
        Self::from_files(&[
            [&std::env::var("HOME").unwrap(), ".ssh", "config"]
                .iter()
                .collect::<PathBuf>()
                .as_path(),
            ["/etc", "ssh", "ssh_config"]
                .iter()
                .collect::<PathBuf>()
                .as_path(),
        ])
    }

    pub fn from_file<P>(path: P) -> Result<Self, Error>
    where
        P: AsRef<Path>,
    {
        Self::from_files(std::iter::once(path))
    }

    pub fn from_files<I, P>(paths: I) -> Result<Self, Error>
    where
        P: AsRef<Path>,
        I: IntoIterator<Item = P>,
    {
        // "merge"-able options:
        // oLocalForward, oRemoteForward, oDynamicForward
        // oSendEnv, oSetEnv
        // oCanonicalDomains
        // oCanonicalizePermittedCNAMEs?
        // oGlobalKnownHostsFile, oUserKnownHostsFile

        struct ReadOpts {}
        impl Default for ReadOpts {
            fn default() -> Self {
                Self {}
            }
        }

        fn readconf_depth<P: AsRef<Path>>(path: P, depth: usize) -> Result<Vec<SSHOption>, Error> {
            if depth > MAX_READCONF_DEPTH {
                return Err(Error::MaxDepthExceeded);
            }

            // The only depth 0 file that gets checked for perms is the user config file
            if depth != 0 {
                let meta = fs::metadata(&path)?;
                let perms = meta.permissions();

                if cfg!(unix) {
                    use std::os::unix::fs::MetadataExt;
                    use std::os::unix::fs::PermissionsExt;
                    // TODO: check against getuid
                    if meta.uid() != 0 && perms.mode() & 0o022 != 0 {
                        return Err(Error::PermissionError);
                    }
                }
            }

            use option::Include::*;
            use option::SSHOption::Include;
            let file = File::open(path)?;
            let mut opts = vec![];
            for line in io::BufReader::new(file).lines() {
                let opt = if let Some(opt) = option::parse_opt(line?)? {
                    opt
                } else {
                    continue;
                };

                match opt {
                    Include(Paths(paths)) => {
                        let mut vec = vec![];

                        let files = paths
                            .into_iter()
                            .filter_map(
                                |p|/* TODO: tilde expansion, sometimes */ glob::glob(&p).ok(),
                            )
                            .flatten()
                            .filter_map(|p| p.ok());

                        for f in files {
                            // TODO "anchoring"
                            match readconf_depth(f, depth + 1) {
                                Err(Error::Read(_)) => continue,
                                err @ Err(_) => return err,

                                Ok(o) => vec.extend(o),
                            }
                        }
                        opts.push(Include(Opts(vec)))
                    }

                    opt => opts.push(opt),
                }
            }
            Ok(opts)
        }

        let mut config = vec![];

        for path in paths {
            config.extend(readconf_depth(path, 0)?);
        }

        config.extend(SSHConfig::default().0.into_iter().filter(|_| true));

        Ok(SSHConfig(config))
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

#[cfg(test)]
mod test {
    use super::{option, SSHConfig, SSHOption, MAX_READCONF_DEPTH};
    use std::fs;
    use tempfile::tempdir;

    #[test]
    // TODO remove and/or figure out how to chroot in CI
    #[cfg(not(CI))]
    fn it_works() {
        let cfg = SSHConfig::from_default_files().expect("read failed");
        assert_eq!(
            cfg.0[..6],
            [
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

    #[test]
    fn includes() {
        let dir = tempdir().unwrap();
        fs::write(dir.path().join("file_0"), r"Host example.com").expect("failed writing config");

        for rdepth in 1..(MAX_READCONF_DEPTH + 2) {
            let file = dir.path().join(format!("file_{}", rdepth));
            fs::write(
                file,
                format!(
                    "Include {}",
                    dir.path().join(format!("file_{}", rdepth - 1)).display(),
                ),
            )
            .expect("failed writing config");
        }

        assert_eq!(
            SSHConfig::from_file(dir.path().join("file_1"))
                .expect("failed to read config")
                .0
                .first()
                .expect("should have at least one element"),
            &SSHOption::Include(option::Include::Opts(vec![SSHOption::Host(String::from(
                "example.com",
            ))])),
        );

        let mut deep_cfg =
            SSHConfig::from_file(dir.path().join(format!("file_{}", MAX_READCONF_DEPTH)))
                .expect("failed to read config")
                .0
                .into_iter()
                .next()
                .unwrap();
        for d in 1..MAX_READCONF_DEPTH {
            deep_cfg = match deep_cfg {
                SSHOption::Include(option::Include::Opts(mut opts)) => {
                    assert_eq!(opts.len(), 1);
                    opts.pop().unwrap()
                }
                bad @ _ => panic!("failed to unwrap Include: saw {:?} at depth {}", bad, d),
            }
        }

        let err = SSHConfig::from_file(dir.path().join(format!("file_{}", MAX_READCONF_DEPTH + 1)))
            .expect_err("parse should have failed");

        assert_eq!(
            std::mem::discriminant(&err),
            std::mem::discriminant(&super::Error::MaxDepthExceeded),
        )
    }
}
