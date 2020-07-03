use std::fs;
use std::io;
use std::io::{BufRead, Write};
use std::process::{Command, Stdio};
use tempfile::tempdir;

#[test]
fn hello_world() {
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

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com")
}

#[test]
fn hello_world3() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    // this is weird, but ??
    fs::write(&cfg_file, r#"=user eve"#).expect("failed writing config");

    let mut child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    child.wait().expect("child wasn't running");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.nth(0).unwrap().unwrap(), "user eve")
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

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com")
}

#[test]
fn hello_world5() {
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

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname example.com")
}

#[test]
fn quoted_token_config() {
    let dir = tempdir().unwrap();
    let cfg_file = dir.path().join("hello_world6_config");
    // this is valid, but `hello" "world is not
    fs::write(
        &cfg_file,
        r#"hostname hello" world"
    port 2"3""#,
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

    assert_eq!(lines.nth(1).unwrap().unwrap(), "hostname hello world");
    assert_eq!(lines.next().unwrap().unwrap(), "port 23");
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
