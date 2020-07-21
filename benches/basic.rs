use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::iter;

pub fn to_ascii_lowercase(c: &mut Criterion) {
    let mut g = c.benchmark_group("to_ascii_lowercase");
    static KB: usize = 1024;

    for size in [32, KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        g.throughput(Throughput::Bytes(*size as u64));
        g.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let s = iter::repeat('A').take(size).collect::<String>();
            b.iter(|| s.to_ascii_lowercase());
        });
    }
    g.finish();
}

pub fn make_ascii_lowercase(c: &mut Criterion) {
    let mut g = c.benchmark_group("make_ascii_lowercase");
    static KB: usize = 1024;

    for size in [32, KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        g.throughput(Throughput::Bytes(*size as u64));
        g.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut s = iter::repeat('A').take(size).collect::<String>();
            b.iter(move || s.make_ascii_lowercase());
        });
    }
    g.finish();
}

pub fn concat_and_lowercase(c: &mut Criterion) {
    static KB: usize = 1024;

    let mut g = c.benchmark_group("blurg");
    for size in [32, KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        g.throughput(Throughput::Bytes(*size as u64));
        g.bench_with_input(
            BenchmarkId::new("to_ascii_lowercase: concat", size),
            size,
            |b, &size| {
                let s1 = iter::repeat('A').take(size / 2).collect::<String>();
                let s2 = iter::repeat('A').take(size / 2).collect::<String>();
                b.iter(|| format!("{}{}", s1, s2).to_ascii_lowercase());
            },
        );
    }
    // g.finish();

    // let mut g = c.benchmark_group("concat: to_ascii_lowercase");
    for size in [32, KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        g.throughput(Throughput::Bytes(*size as u64));
        g.bench_with_input(
            BenchmarkId::new("concat: to_ascii_lowercase", size),
            size,
            |b, &size| {
                let s1 = iter::repeat('A').take(size / 2).collect::<String>();
                let s2 = iter::repeat('A').take(size / 2).collect::<String>();
                b.iter(|| format!("{}{}", s1.to_ascii_lowercase(), s2.to_ascii_lowercase()));
            },
        );
    }
    g.finish();
}

criterion_group!(
    benches,
    to_ascii_lowercase,
    make_ascii_lowercase,
    concat_and_lowercase
);
criterion_main!(benches);
