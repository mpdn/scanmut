use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::RngCore;
use rand_pcg::Lcg128Xsl64;
use scanmut::ScanMut;

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = Lcg128Xsl64::new(0xcafef00dd15ea5e5, 0xa02bdbf7bb3c0a7ac28fa16a64abf96);

    let items: Vec<_> = (0..100000).map(|_| rng.next_u32()).collect();

    let mut insertions: Vec<_> = (0..10000)
        .map(|_| ((rng.next_u32() as usize) % items.len(), rng.next_u32()))
        .collect();

    insertions.sort_by(|a, b| b.cmp(a));

    let removal_limit = std::u32::MAX / 10;

    let removals: Vec<_> = items
        .iter()
        .enumerate()
        .filter(|&(_, &x)| x < removal_limit)
        .map(|(i, _)| i)
        .collect();

    c.bench_function("multi_insert", |b| {
        b.iter(|| {
            let mut v = Vec::with_capacity(items.len() + insertions.len());
            v.extend(items.iter().clone());
            v = black_box(v);
            v.multi_insert(insertions.iter().cloned());
            black_box(v);
        })
    });

    c.bench_function("multi_remove", |b| {
        b.iter(|| {
            let mut v = black_box(items.clone());
            v.multi_remove(black_box(&removals).iter().cloned(), drop);
            black_box(v);
        })
    });

    // Attempt at a slightly more fair comparison to `retain` where the comparison is done within
    // the benchmark. Somehow this is still faster than `retain` as of writing.
    c.bench_function("multi_remove_indexes", |b| {
        b.iter(|| {
            let mut v = black_box(items.clone());

            let removals: Vec<usize> = v
                .iter()
                .enumerate()
                .filter(|&(_, &x)| x < removal_limit)
                .map(|(i, _)| i)
                .collect();

            v.multi_remove(removals.into_iter(), drop);
            black_box(v);
        })
    });

    c.bench_function("retain", |b| {
        b.iter(|| {
            let mut v = black_box(items.clone());
            v.retain(|&x| x >= removal_limit);
            black_box(v);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
