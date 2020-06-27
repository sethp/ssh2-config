use std::fs;
use std::io;
use std::io::{BufRead, Write};
use std::process::{Command, Stdio};
use tempdir::TempDir;

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
    let child = Command::new("ssh")
        .args(&["-T", "-F", "/dev/null", "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.next().unwrap().unwrap(), "user seth")

    // io::Lines<io::BufReader
    //
    // assert!(output.status.success());
    // io::stdout().write_all(&output.stdout).unwrap();
    // io::stderr().write_all(&output.stderr).unwrap();
}

#[test]
fn hello_world3() {
    let dir = TempDir::new("foobar").unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    // this is weird, but ??
    fs::write(&cfg_file, r#"=user eve"#).expect("failed writing config");

    let child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.next().unwrap().unwrap(), "user eve")
}

#[test]
fn hello_world4() {
    let dir = TempDir::new("foobar").unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    // this is weird, but ??
    fs::write(&cfg_file, r#"=# comment"#).expect("failed writing config");

    let child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.next().unwrap().unwrap(), "user seth")
}

#[test]
fn hello_world5() {
    let dir = TempDir::new("foobar").unwrap();
    let cfg_file = dir.path().join("hello_world3_config");
    // this is weird, but ??
    fs::write(&cfg_file, r#"=# comment"#).expect("failed writing config");

    let child = Command::new("ssh")
        .args(&["-T", "-F", cfg_file.to_str().unwrap(), "-G", "example.com"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("failed to execute process");

    let mut lines = io::BufReader::new(child.stdout.expect("no stdout")).lines();

    assert_eq!(lines.next().unwrap().unwrap(), "user seth")
}
