use ssh2_config::{
    option::{self, parse_opt, SSHOption},
    Error, SSHConfig, MAX_READCONF_DEPTH,
};
use std::fs;
use std::io;
use std::io::{BufRead, Cursor, Write};
use std::process::{Command, Stdio};
use tempfile::tempdir;

#[test]
fn hello_world() {
    assert!(Command::new("ssh")
        .args(&["-V"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .status()
        .expect("failed to execute process")
        .success());

    let output = Command::new("ssh")
        .args(&["-T", "-F", "/dev/null", "-G", "example.com"])
        .output()
        .expect("failed to execute process");

    assert!(output.status.success());
    io::stdout().write_all(&output.stdout).unwrap();
    io::stderr().write_all(&output.stderr).unwrap();
}

#[test]
fn hello_world2() {
    let mut child = Command::new("ssh")
        .args(&["-T", "-F", "/dev/null", "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com");
}

#[test]
fn hello_world3() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    fs::write(&cfg_file, r#"=user eve"#).expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(0).unwrap().unwrap(), "user eve");
}

#[test]
fn hello_world4() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    // this is weird, but ??
    fs::write(&cfg_file, r#"=# comment"#).expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");
    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com");
}

#[test]
fn trailing_zero_width() {
    // These happen because the check for "garbage" only looks at the _next_ argument,
    // and it allows an empty string. In SSH-config land, the three ways to spell "empty
    // string" are `""`, `==`, and `..."=` (though because the `"` and `=` greedily
    // consume any following blanks `..." =` and `= =` are also empty arguments).
    let cases = r#"
user eve==anything may appear after a double equals after the last expected arg
user eve ==including double equals preceded by blanks
user eve = =or separated by blanks
user "eve"=or a single equals, if the last arg is quoted
user "eve" =including a single equals preceded by blanks
user eve ""or after an empty quoted value
"#
    .lines()
    .filter(|s| !s.is_empty());
    let mut i = 0;
    let dir = tempdir().unwrap();
    for case in cases {
        let cfg_file = dir.path().join(format!("trailing_values_config_{}", i));
        i = i + 1;

        fs::write(&cfg_file, case).expect("failed writing config");

        let mut child = Command::new("ssh")
            .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
            .env("USER", "user_from_environment")
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("failed to execute process");

        child.wait().expect("child wasn't running");

        let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

        assert_eq!(
            lines
                .next()
                .expect(format!("invalid input: {:?}", case).as_ref())
                .unwrap(),
            "user eve"
        );

        assert_eq!(
            case.parse::<SSHOption>()
                .expect(format!("failed to parse {:?}", case).as_str()),
            SSHOption::User(String::from("eve")),
            "failed on input {:?}",
            case,
        )
    }
}

#[test]
fn leading_zero_width() {
    let cases = r#"
==anything goes after two empty strings
""= or the other spellings for zero value keywords are fine too
"""" including quadruple-quote
=  = don't forget spaces
""  = or the other spaces
""  "" or the other other spaces
"#
    .lines()
    .filter(|s| !s.is_empty());
    let mut i = 0;
    let dir = tempdir().unwrap();
    for case in cases {
        let cfg_file = dir.path().join(format!("trailing_values_config_{}", i));
        i = i + 1;

        fs::write(&cfg_file, case).expect("failed writing config");

        let mut child = Command::new("ssh")
            .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("failed to execute process");

        assert!(child.wait().expect("child wasn't running").success());

        assert!(
            parse_opt(case)
                .expect(format!("failed to parse {:?}", case).as_str())
                .is_none(),
            "failed on input {:?}",
            case,
        )
    }
}

#[test]
fn hello_world5() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("hello_world5_config");
    fs::write(
        &cfg_file,
        r#"=# comment
port 22"#,
    )
    .expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com");
    assert_eq!(lines.next().unwrap().unwrap(), "port 22");
}

#[test]
// see: https://github.com/sethp/ssh2-config/issues/16
#[cfg(not(CI))]
fn test_named_ports() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("named_ports_config");
    fs::write(&cfg_file, r#"port ssh"#).expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com");
    assert_eq!(lines.next().unwrap().unwrap(), "port 22");
}

#[test]
fn quoted_token_config() {
    let valid = r#"
User eve
User=eve
User "eve"
User="eve"
"User"eve
"User""eve"
U"ser" eve
U"ser" "eve"
U"ser" e"ve"
U"ser""eve"
U"ser"e"ve"
"#
    .lines()
    .filter(|s| !s.is_empty());
    let mut i = 0;
    let dir = tempdir().unwrap();
    for case in valid {
        let cfg_file = dir.path().join(format!("quoted_token_config_{}", i));
        i = i + 1;

        fs::write(&cfg_file, case).expect("failed writing config");

        let mut child = Command::new("ssh")
            .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("failed to execute process");

        child.wait().expect("child wasn't running");

        let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

        assert_eq!(
            lines
                .next()
                .expect(format!("invalid input: {:?}", case).as_ref())
                .unwrap(),
            "user eve"
        );

        assert_eq!(
            case.parse::<SSHOption>()
                .expect(format!("failed to parse {:?}", case).as_str()),
            SSHOption::User(String::from("eve")),
            "failed on input {:?}",
            case,
        )
    }
}

#[test]
fn multi_line_quoted_token_fails() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("multi_line_quoted_token_config");
    fs::write(
        &cfg_file,
        r#"hostname "foo
    bar""#,
    )
    .expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to execute process");

    let exit = child.wait().expect("child wasn't running");
    assert!(!exit.success());

    let mut lines = io::BufReader::new(child.stdout.expect("bad stdout")).lines();
    assert!(lines.next().is_none());
    let mut err_lines = io::BufReader::new(child.stderr.expect("bad stderr")).lines();

    assert!(&err_lines
        .next()
        .unwrap()
        .unwrap()
        .ends_with("line 1: Missing argument."));
}

#[test]
fn comments() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("comments");
    fs::write(
        &cfg_file,
        r#"
# this is a comment
=# this too is a comment
=   #comment
hostname "example.com""#,
    )
    .expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com");
}

#[test]
fn bad_comments() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("bad_comment");
    fs::write(&cfg_file, r#"hostname "example.com" # end of line comment"#)
        .expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to execute process");

    let exit = child.wait().expect("child wasn't running");
    assert!(!exit.success());

    let mut lines = io::BufReader::new(child.stdout.expect("bad stdout")).lines();
    assert!(lines.next().is_none());
    let mut err_lines = io::BufReader::new(child.stderr.expect("bad stderr")).lines();

    let err = &err_lines.next().unwrap().unwrap();

    assert!(
        err.ends_with("line 1: garbage at end of line; \"#\"."),
        "Got: {}",
        err
    );
}

#[test]
fn includes() {
    let dir = tempdir().unwrap();
    let subdir = dir.path().join("subdir");
    fs::create_dir(&subdir).unwrap();
    fs::write(dir.path().join("file_0"), r"").expect("failed writing config");
    fs::write(dir.path().join("file_1"), r"").expect("failed writing config");
    let cases = &[
        format!("Include"),
        format!("Include {}", subdir.display()),
        format!("Include {}", dir.path().join("file_0").display()),
        format!("Include {}", dir.path().join("file_[bl").display()),
        format!(
            "Include {} {}",
            dir.path().join("file_*").display(),
            dir.path().join("f*").display()
        ),
        format!("Include file_dne"),
    ];

    for case in cases {
        let path = dir.path().join("cfg");
        fs::write(&path, case).expect("failed writing config");

        let output = Command::new("ssh")
            .args(&["-T", "-F", path.to_str().unwrap(), "-G", "example.com"])
            .output()
            .expect("failed to execute process");
        io::stderr().write_all(&output.stderr).unwrap();
        assert!(output.status.success());

        SSHConfig::from_file(&path).expect("failed to read config");
    }
}

#[test]
fn deep_includes() {
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

    let deep_cfg_file = dir.path().join(format!("file_{}", MAX_READCONF_DEPTH));
    let mut deep_cfg = SSHConfig::from_file(&deep_cfg_file)
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

    let output = Command::new("ssh")
        .args(&[
            "-T",
            "-F",
            deep_cfg_file.to_str().unwrap(),
            "-G",
            "example.com",
        ])
        .output()
        .expect("failed to execute process");
    assert!(output.status.success());

    let bad_file = dir.path().join(format!("file_{}", MAX_READCONF_DEPTH + 1));
    let err = SSHConfig::from_file(&bad_file).expect_err("parse should have failed");

    assert_eq!(
        std::mem::discriminant(&err),
        std::mem::discriminant(&Error::MaxDepthExceeded),
    );

    let output = Command::new("ssh")
        .args(&["-T", "-F", bad_file.to_str().unwrap(), "-G", "example.com"])
        .output()
        .expect("failed to execute process");

    assert!(!output.status.success());
    let mut lines = io::BufReader::new(Cursor::new(output.stdout)).lines();
    assert!(lines.next().is_none());
    let mut err_lines = io::BufReader::new(Cursor::new(output.stderr)).lines();

    let err = &err_lines.next().unwrap().unwrap();
    assert!(
        err.ends_with("Too many recursive configuration includes"),
        "Got: {}",
        err
    );
}
