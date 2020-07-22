use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ssh2_config::option::{
    parse_always_alloc, parse_regex_groups, parse_regex_ladder, parse_regex_onig_split,
    parse_tokens, parse_tokens_no_vec, parse_tokens_no_vec2,
};
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
            BenchmarkId::new("parse_always_alloc", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_always_alloc(s).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_regex_onig_split", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_regex_onig_split(s, |_, _| ()).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_regex_groups", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_regex_groups(s, |_, _| ()).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_regex_ladder", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_regex_ladder(s, |_, _| ()).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_tokens", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_tokens(s, |_, _| ()).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_tokens_no_vec", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_tokens_no_vec(s, |_, _| ()).expect("ok")),
        );
        g.bench_with_input(
            BenchmarkId::new("parse_tokens_no_vec2", format!("{:?}", case)),
            case,
            |b, s| b.iter(|| parse_tokens_no_vec2(s, |_, _| ()).expect("ok")),
        );
    }

    g.finish()
}

criterion_group!(ssh_options, bench_parse_tokens);
criterion_main!(ssh_options);
