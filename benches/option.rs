use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ssh2_config::option;
use ssh2_config::option::simple;
use ssh2_config::option::{parse_tokens, Arguments};
use std::time::Duration;

pub fn bench_parse_tokens(c: &mut Criterion) {
    const TEST_CASES: &[&str] = &[
        r#"key value"#,
        r#"KEY value"#,
        r#""KEY"value"#,
        r#""KEY""value""#,
        r#"KEYPART1"KEYPART2" value"#,
        r#"KEYPART1"KEYPART2"value"#,
        r#"KEYPART1"KEYPART2""value""#,
    ];
    let mut g = c.benchmark_group("Option tokenizing");
    g.measurement_time(Duration::from_secs(10));

    for case in TEST_CASES {
        g.bench_with_input(
            BenchmarkId::new("parse_tokens", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_tokens(s, |_, args| args.map_next(|_, _| Ok(()))).expect("ok")),
        );
    }

    g.finish()
}

pub fn bench_parse_opt(c: &mut Criterion) {
    const TEST_CASES: &[&str] = &[r#"Hostname example.com"#];
    let mut g = c.benchmark_group("Option parsing");
    g.measurement_time(Duration::from_secs(10));
    for case in TEST_CASES {
        g.bench_function(
            BenchmarkId::new("option::parse_opt", format!("{:?}", case)),
            |b| b.iter(|| option::parse_opt(case).expect("ok").expect("found")),
        );

        g.bench_function(
            BenchmarkId::new("simple::parse_opt", format!("{:?}", case)),
            |b| b.iter(|| simple::parse_opt(case).expect("ok").expect("found")),
        );
    }
    g.finish()
}

criterion_group!(ssh_options, bench_parse_tokens, bench_parse_opt);
criterion_main!(ssh_options);
