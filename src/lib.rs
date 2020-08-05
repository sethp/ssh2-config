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

// https://man.openbsd.org/OpenBSD-current/man5/ssh_config.5

#[allow(missing_docs)]
pub struct SSHConfig {}

#[allow(missing_docs)]
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
