use graph::nauty::orbits;
use graph::subgraphs::subgraphs_orbits;
use graph::GraphNauty;
use graph::{Graph, GraphIter};
use std::collections::HashMap;
use std::time::Instant;
use std::ops::Deref;

type ft = Vec<Vec<u64>>;

trait Fixed: Deref<Target=ft> {
    fn new() -> Self;
    fn fix(&mut self, v: u64);
    fn unfix(&mut self);
}

struct FixedSame {
    v: ft
}

impl Fixed for FixedSame {
    fn new() -> Self {
        FixedSame {
            v: vec![vec![]]
        }
    }

    fn fix(&mut self, v: u64) {
        self.v[0].push(v);
    }

    fn unfix(&mut self) {
        self.v[0].pop();
    }
}

impl Deref for FixedSame {
    type Target=ft;

    fn deref(&self) -> &Self::Target {
        &self.v
    }
}

struct FixedDiff {
    v: ft,
}

impl Fixed for FixedDiff {
    fn new() -> Self {
        FixedDiff {
            v: Vec::new()
        }
    }

    fn fix(&mut self, v: u64) {
        self.v.push(vec![v]);
    }

    fn unfix(&mut self) {
        self.v.pop();
    }
}

impl Deref for FixedDiff {
    type Target=ft;

    fn deref(&self) -> &Self::Target {
        &self.v
    }
}

fn test_strategy<F: Fixed>(n: u64, mut fixed: F) {
    let mut g = GraphNauty::new(n);
    for i in 0..n {
        g.add_edge(i, (i + 1) % n);
    }
    for i in orbits(&g, &fixed) {
        fixed.fix(i);
        for j in orbits(&g, &fixed) {
            if i != j && g.is_edge(i, j) {
                fixed.fix(j);
                for k in orbits(&g, &fixed) {
                    if k != i && k != j && !g.is_edge(k, i) {
                        fixed.fix(k);
                        for l in orbits(&g, &fixed) {
                            if l != i && l != j && l != k && !g.is_edge(l, j) && g.is_edge(k, l) {
                                println!("{} {} {} {}", i, j, k, l);
                            }
                        }
                        fixed.unfix();
                    }
                }
                fixed.unfix();
            }
        }
        fixed.unfix();
    }
}

fn main() {
    let n = 6;
    test_strategy(6, FixedSame::new());
    println!("---");
    test_strategy(6, FixedDiff::new());
    println!("---");
    let mut g = GraphNauty::new(n);
    for i in 0..n {
        g.add_edge(i, (i + 1) % n);
    }
    let mut g2 = GraphNauty::new(4);
    g2.add_edge(0, 1);
    g2.add_edge(2, 3);
    let res = subgraphs_orbits(&g, &g2).collect::<Vec<Vec<_>>>();
    println!("{:?}", res);
}
