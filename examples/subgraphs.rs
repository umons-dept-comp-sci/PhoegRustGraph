use graph::nauty::orbits;
use graph::subgraphs::subgraphs_orbits;
use graph::GraphNauty;
use graph::{Graph, GraphConstructible, GraphIter};
use std::collections::HashMap;
use std::time::Instant;
use std::ops::Deref;

fn main() {
    let mut g = GraphNauty::new(5);
    g.add_edge(0, 1);
    g.add_edge(1, 2);
    g.add_edge(2, 0);
    g.add_edge(1, 3);
    let mut g2 = GraphNauty::new(3);
    g2.add_edge(0, 1);
    g2.add_edge(1, 2);
    g2.add_edge(2, 0);
    println!("{:?}", subgraphs_orbits(&g, &g2).collect::<Vec<_>>());
}
