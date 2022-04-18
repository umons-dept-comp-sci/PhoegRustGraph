use graph::GraphNauty;
use graph::format::from_g6;
use std::fs::File;
use std::io::{self, BufRead};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn get_lines() -> Vec<String> {
    let file = File::open("biggraphs.g6").unwrap();
    let lines: Vec<String> = io::BufReader::new(file).lines().map(|x| x.unwrap()).collect();
    lines
}

fn bench_from_g6(c: &mut Criterion) {
    let lines = get_lines();
    c.bench_function("from_g6", |b| b.iter(|| lines.iter().map(|x| from_g6(x).unwrap()).collect::<Vec<GraphNauty>>()));
}

fn bench_parse_graph6(c: &mut Criterion) {
    let lines = get_lines();
    c.bench_function("parse_graph6", |b| b.iter(|| lines.iter().map(|x| GraphNauty::parse_graph6(x)).collect::<Vec<GraphNauty>>()));
}

criterion_group!(benches, bench_from_g6, bench_parse_graph6);
criterion_main!(benches);
