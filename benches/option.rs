use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ssh2_config::option::parse_tokens;
use std::time::Duration;

pub fn bench_parse_tokens(c: &mut Criterion) {
    const TEST_CASES: &[&str] = &[
        r#"key value"#,
        r#"KEY value"#,
        r#""KEY" "value""#,
        r#"KEYPART1"KEYPART2" value"#,
        r#"KEYPART1"KEYPART2" VALUEPART1"VALUEPART2""#,
    ];
    let mut g = c.benchmark_group("Option tokenizing");
    g.measurement_time(Duration::from_secs(10));

    for case in TEST_CASES {
        g.bench_with_input(
            BenchmarkId::new("parse_tokens", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_tokens(s, |_, _| Ok(())).expect("ok")),
        );
    }

    g.finish()
}

criterion_group!(ssh_options, bench_parse_tokens);
criterion_main!(ssh_options);
