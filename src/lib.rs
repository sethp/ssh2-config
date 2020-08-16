//! ```no_run
//! use ssh2::Session;
//! use ssh2_config::SSHConfig;
//!
//! // Retrieve config for local SSH server
//! let sess = SSHConfig::from_file("/path/to/ssh/config") // equivalent to OpenSSH's `-F`
//!                 .for_host("127.0.0.1")
//!                 .connect_with_auth();
//!
//! // Make sure we're authenticated
//! assert!(sess.authenticated());
//! ```
//!
//! The guiding rule for this crate is that we may accept configurations OpenSSH won't, but
//! we won't reject configurations that OpenSSH would consider valid. The lone exception to
//! that rule is that we do require that all config files and file paths are valid unicode.

// TODO
// #![doc(html_root_url = "https://docs.rs/ssh2-config")]
#![deny(missing_docs, unused_results)]
#![cfg_attr(test, deny(warnings))]

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(feature = "with_libc")]
extern crate libc;

#[cfg(feature = "with_libc")]
use {libc::getuid, tilde_expand::tilde_expand};

#[cfg(not(feature = "with_libc"))]
unsafe fn getuid() -> u32 {
    unimplemented!()
}

#[cfg(all(unix, not(feature = "with_libc")))]
fn tilde_expand(s: &[u8]) -> Vec<u8> {
    use std::os::unix::ffi::OsStringExt;
    if s.starts_with(b"~/") {
        let mut r = homedir().into_vec();
        r.extend(&s[2..]);
        r
    } else {
        Vec::from(s)
    }
}

/// Individual SSH config options, e.g. `Port 22` or `Hostname example.com`
pub mod option;

pub use option::SSHOption;

use std::ffi::OsString;
use std::fmt;
use std::fs::{self, File};
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

#[derive(Debug)]
/// SSHConfig represents a parsed ssh configuration. The format is roughly documented in [ssh_config(5)], and
/// exhaustively documented in this crate's option module.
///
/// [ssh_config(5)]: https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5
///
/// A config may include multiple copies of options and inactive options: TODO examples, details
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
    BadInclude(String),
    PathInvalidUnicode(PathBuf, Option<std::str::Utf8Error>),
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
            Error::BadInclude(ref path) => write!(f, "bad include path: {}", path),

            Error::PathInvalidUnicode(ref path, None) => {
                write!(f, "invalid unicode in path: {}", path.to_string_lossy())
            }
            Error::PathInvalidUnicode(ref path, Some(ref err)) => write!(
                f,
                "invalid unicode in path: {} ({})",
                path.to_string_lossy(),
                err
            ),
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

impl From<std::string::FromUtf8Error> for Error {
    #[cfg(unix)]
    fn from(e: std::string::FromUtf8Error) -> Self {
        use std::os::unix::ffi::OsStringExt;
        let err = e.utf8_error();
        let path = PathBuf::from(OsString::from_vec(e.into_bytes()));

        Error::PathInvalidUnicode(path, Some(err))
    }
}

#[cfg(all(unix, feature = "with_libc"))]
fn homedir() -> OsString {
    use std::ffi::{CStr, OsStr};
    use std::os::unix::ffi::OsStrExt;
    let (pw, uid) = unsafe {
        // SAFETY: getuid can't fail
        let uid = libc::getuid();
        (libc::getpwuid(uid), uid)
    };
    if pw.is_null() {
        panic!("No user exists for uid {}", uid)
    }
    // SAFETY: pw is not null
    let dir = unsafe { CStr::from_ptr((*pw).pw_dir) };
    // SAFETY: we copy the bytes with `to_os_string` before returning
    // This is important because `getpwuid` returns the address of a
    // static region that would be overwritten by future `getpw*` calls
    OsStr::from_bytes(dir.to_bytes()).to_os_string()
}

#[cfg(not(feature = "with_libc"))]
fn homedir() -> OsString {
    std::env::var_os("HOME").expect("HOME environment variable must be set")
}

#[allow(missing_docs)]
impl SSHConfig {
    pub fn from_default_files() -> Result<Self, Error> {
        Self::from_files(
            [&Self::user_config(), &Self::system_config()]
                .iter()
                .filter(|p| p.exists()),
        )
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

        let mut config = vec![];

        for path in paths {
            // TODO: we need to track the "file" boundary, since every
            // file starts off as matching everything
            config.extend(readconf_depth(
                &path,
                ReadMeta {
                    depth: 0,
                    // the only non-"user" config is the system-wide `/etc/ssh/ssh_config` file
                    user_config: *path.as_ref() != Self::system_config(),
                },
            )?);
        }

        // TODO: this is too early to apply defaults anyway – seeing a value in the config
        // doesn't mean it's "active"
        config.extend(Self::default().0.into_iter().filter(|_| true));

        Ok(Self(config))
    }

    pub fn for_host(self: &Self, host: &str) -> Self {
        fn host_matches(h1: &str, h2: &str) -> bool {
            h1 == h2 || h1 == "*" || h2 == "*"
        }

        let mut last_host = None;
        return Self(
            self.0
                .iter()
                .filter(|opt| match opt {
                    SSHOption::Host(h) => {
                        last_host = Some(h);
                        false
                    }
                    _ => last_host.map(|h| host_matches(h, host)).unwrap_or(true),
                })
                .map(|opt| opt.clone())
                .collect(),
        );

        // HashMap<std::mem::Discriminant<SSHOption>, SSHOption>
        // 1. Get me all the IdentityFile directives
        // 2. insert-or-merge
        // 3. Iterate over every option and "apply" it to an ssh session
    }

    pub fn with_config_file(self: &Self, _: &str) -> Self {
        unimplemented!()
    }

    pub fn connect_with_auth(self: &Self) -> ssh2::Session {
        unimplemented!()
    }

    fn user_dir() -> PathBuf {
        [homedir(), OsString::from(".ssh")].iter().collect()
    }

    fn system_dir() -> PathBuf {
        ["/etc", "ssh"].iter().collect()
    }

    pub fn user_config() -> PathBuf {
        Self::user_dir().join("config")
    }

    pub fn system_config() -> PathBuf {
        Self::system_dir().join("ssh_config")
    }
}

// Similar to SSH's `flags` parameter
#[derive(Copy, Clone)]
struct ReadMeta {
    depth: usize,
    user_config: bool,
}

fn readconf_depth<P: AsRef<Path>>(path: P, meta: ReadMeta) -> Result<Vec<SSHOption>, Error> {
    if meta.depth > MAX_READCONF_DEPTH {
        return Err(Error::MaxDepthExceeded);
    }

    // The only depth 0 file that gets checked for perms is the user config file
    if meta.depth > 0 || *path.as_ref() == SSHConfig::user_config() {
        let meta = fs::metadata(&path)?;
        let perms = meta.permissions();

        if cfg!(unix) {
            use std::os::unix::fs::MetadataExt;
            use std::os::unix::fs::PermissionsExt;
            if (meta.uid() != 0
                && if cfg!(feature = "with_libc") {
                    // SAFETY: getuid can never fail
                    meta.uid() != unsafe { getuid() }
                } else {
                    false
                })
                || perms.mode() & 0o022 != 0
            {
                return Err(Error::PermissionError);
            }
        }
    }

    use option::Include::*;
    use option::SSHOption::Include;
    let file = File::open(&path)?;
    let _filename = if let Some(s) = path.as_ref().to_str() {
        s
    } else {
        return Err(Error::PathInvalidUnicode(path.as_ref().to_path_buf(), None));
    };
    let mut opts = vec![];
    for line in io::BufReader::new(file).lines() {
        let opt = if let Some(opt) = option::parse_opt(line?)? {
            opt
        } else {
            continue;
        };

        match opt {
            Include(Paths(paths)) => {
                let mut globbed = vec![];
                for path in paths {
                    /*
                     * Ensure all paths are anchored. User configuration
                     * files may begin with '~/' but system configurations
                     * must not. If the path is relative, then treat it
                     * as living in ~/.ssh for user configurations or
                     * /etc/ssh for system ones.
                     */
                    let p = match path {
                        p if p.starts_with('~') && !meta.user_config => {
                            return Err(Error::BadInclude(p));
                        }
                        p if p.starts_with('~') => String::from_utf8(tilde_expand(p.as_bytes()))?,
                        p if !Path::new(&p).has_root() => {
                            let anchor = if meta.user_config {
                                SSHConfig::user_dir()
                            } else {
                                SSHConfig::system_dir()
                            };
                            let path = anchor.join(p);

                            if let Some(s) = path.to_str() {
                                s.to_owned()
                            } else {
                                return Err(Error::PathInvalidUnicode(path, None));
                            }
                        }
                        p => p,
                    };

                    globbed.push(if let Ok(g) = glob::glob(&p) {
                        g
                    } else {
                        continue;
                    });
                }

                let files = globbed.into_iter().flatten().filter_map(|p| p.ok());
                let mut vec = vec![];
                let mut m = meta;
                m.depth += 1;
                for f in files {
                    match readconf_depth(f, m) {
                        Err(Error::Read(e)) if e.kind() == io::ErrorKind::InvalidData => {
                            return Err(e.into())
                        }
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
        let expect = [
            SSHOption::Host(String::from("github.com")),
            SSHOption::User(String::from("git")),
            SSHOption::Host(String::from("bitbucket.org")),
            SSHOption::User(String::from("git")),
            SSHOption::Include(option::Include::Opts(vec![])),
            SSHOption::Host(String::from("*")),
            SSHOption::SendEnv(vec![
                option::Env::Send(String::from("LANG")),
                option::Env::Send(String::from("LC_*")),
            ]),
        ];
        assert_eq!(cfg.0[..expect.len()], expect)
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

    #[test]
    fn config_matching() {
        use SSHOption::*;
        let cfg = SSHConfig(vec![
            Host(String::from("example.com")),
            User(String::from("example_ssh_user")),
            Host(String::from("*")),
            User(String::from("ssh_user")),
        ]);

        assert_eq!(
            cfg.for_host("127.0.0.1").0,
            vec![User(String::from("ssh_user"))]
        );
        assert_eq!(
            cfg.for_host("example.com").0,
            vec![User(String::from("example_ssh_user"))]
        );
    }

    #[test]
    fn whatsup() {
        use std::collections::HashMap;

        let input = vec![
            SSHOption::User(String::from("seth")),
            SSHOption::Port(16),
            SSHOption::User(String::from("eric")),
        ];

        let mut mapping: HashMap<std::mem::Discriminant<SSHOption>, SSHOption> = Default::default();

        for opt in input {
            use option::Merge;
            let k = std::mem::discriminant(&opt);

            if let Some(last) = mapping.insert(k, opt) {
                let opt = mapping.remove(&k).unwrap();
                let merged = last.merge(opt);
                assert!(mapping.insert(k, merged).is_none());
            }
        }

        // do something
        if true {
            panic!("{:?}", mapping);
        }

        // mapping[std::mem::discriminant(&SendEnv(vec![]))]

        // mapping[option::Kind::Port]

        let output = Vec::<SSHOption>::new();
        assert_eq!(
            output,
            vec![SSHOption::User(String::from("seth")), SSHOption::Port(16),]
        );

        let mut mapping: HashMap<std::mem::Discriminant<SSHOption>, SSHOption> = Default::default();

        assert!(mapping
            .insert(
                std::mem::discriminant(&SSHOption::User(String::from("this is ignored"))),
                SSHOption::User(String::from("seth")),
            )
            .is_none());

        // mapping.insert()

        panic!("{:?}", mapping)
    }
}
