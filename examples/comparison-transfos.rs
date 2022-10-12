use graph::nauty::orbits;
use graph::GraphNauty;
use graph::subgraphs::subgraphs_orbits;
use graph::{Graph, GraphConstructible, GraphIter};
use std::time::Instant;
use std::collections::HashMap;

fn main() {
    let n = 100;
    let mut g = GraphNauty::new(n);
    for i in g.vertices().skip(1).take((n-2) as usize) {
        for j in g.vertices().take(i as usize) {
            g.add_edge(i, j);
        }
    }
    g.add_edge(0, n-1);
    let mut fixed = vec![vec![]];
    let mut start = Instant::now();
    for i in orbits(&g, &fixed) {
        fixed[0].push(i);
        for j in orbits(&g, &fixed) {
            if i < j && g.is_edge(i, j) {
                println!("{} {}", i, j);
            }
        }
        fixed[0].pop();
    }
    println!("{} ms", start.elapsed().as_millis());
    start = Instant::now();
    let mut g2 = GraphNauty::new(2);
    g2.add_edge(0, 1);
    for v in subgraphs_orbits(&g, &g2) {
        println!("{:?}", v);
    }
    println!("{} ms", start.elapsed().as_millis());
    let mut m = (n-1)*(n-2)/2 + 1;
    let mut edges = Vec::with_capacity(m as usize);
    for i in g.vertices().skip(1).take((n-2) as usize) {
        for j in g.vertices().take(i as usize) {
            edges.push((j, i));
        }
    }
    edges.push((0, n-1));
    start = Instant::now();
    let mut line = GraphNauty::new(m);
    for i in 1..edges.len() {
        for j in 0..i {
            if edges[i].0 == edges[j].0 || edges[i].1 == edges[j].1 || edges[i].0 == edges[j].1 || edges[i].1 == edges[j].0 {
                line.add_edge(i as u64, j as u64);
            }
        }
    }
    start = Instant::now();
    println!("{:?}", orbits(&line, &fixed).iter().map(|x| edges[*x as usize]).collect::<Vec<_>>());
    println!("{} ms", start.elapsed().as_millis());
}
