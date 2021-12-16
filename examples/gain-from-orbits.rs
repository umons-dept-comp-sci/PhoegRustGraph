use graph::format::from_g6;
use graph::nauty::orbits;
use graph::subgraphs::subgraphs_orbits;
use graph::GraphNauty;
use graph::{Graph, GraphIter};
use std::collections::HashMap;
use std::time::Instant;

const GRAPHS6: &[&str] = &[
    r"E???", r"E??G", r"E??W", r"E??w", r"E?@w", r"E?Bw", r"E@?G", r"E?GW", r"E?D_", r"E?CW",
    r"E?Dg", r"E?F_", r"E?Cw", r"E?Fg", r"E?Dw", r"E?Fw", r"E@GW", r"E?d_", r"E?Lo", r"E?NO",
    r"E?Kw", r"E?Sw", r"E?dg", r"E?No", r"E?Lw", r"E?NW", r"E?Nw", r"E?\o", r"E?lo", r"E?^o",
    r"E?\w", r"E?lw", r"E?^w", r"E?~o", r"E?~w", r"E`?G", r"E?So", r"E_GW", r"EGCW", r"EAIW",
    r"EGCw", r"EGEW", r"EGEw", r"EGDw", r"EGFw", r"EIGW", r"E@hW", r"EGSw", r"EAN_", r"E@LW",
    r"ECSw", r"EANg", r"EAMw", r"EALw", r"EANw", r"E@hO", r"E`GW", r"E@N?", r"ECXo", r"E@po",
    r"EGcw", r"E_Kw", r"E@ow", r"E@ro", r"E_Lw", r"E@pw", r"E@rw", r"E@Kw", r"E@NW", r"E@Lw",
    r"E@Nw", r"E_lo", r"E@vo", r"EC\w", r"EAlw", r"E_lw", r"EC^w", r"E@^o", r"E@\w", r"E@lw",
    r"E@^w", r"E@~o", r"E@~w", r"EC\o", r"EIKw", r"EIMw", r"EILw", r"EINw", r"EoSo", r"E`dg",
    r"EKSw", r"EoSw", r"E@lo", r"EELg", r"EPVW", r"EPTw", r"EDZW", r"EDZw", r"ES\o", r"EiKw",
    r"EBzo", r"EImw", r"EBzw", r"EBxw", r"EB\w", r"ED\w", r"EB^w", r"EHuw", r"EElw", r"ED^w",
    r"EB~w", r"Es\o", r"Es\w", r"EFxw", r"EFzw", r"EF~w", r"EwCW", r"E`LW", r"E`ow", r"E`Kw",
    r"E`NW", r"E`Lw", r"E`Nw", r"ETXW", r"E`^o", r"E`\w", r"EQlw", r"E`lw", r"E`^w", r"E`~o",
    r"E`~w", r"ED^_", r"E`lo", r"EqLw", r"EqNw", r"E{Sw", r"Eqlw", r"EMlw", r"Ed^w", r"ER~w",
    r"Ed\w", r"ET\w", r"ER^w", r"EJ]w", r"EJ\w", r"EJ^w", r"EJ~w", r"EN~w", r"ER~o", r"Er\w",
    r"Et\w", r"Er^w", r"E}lw", r"Er~w", r"E^~w", r"E~~w",
];

fn naive_edges(g: &GraphNauty) -> usize {
    let mut num = 0;
    let n = g.order();
    for i in 1..n {
        for j in 0..i {
            if g.is_edge(i, j) {
                num += 1;
            }
        }
    }
    num
}

fn orbits_edges(g: &GraphNauty) -> usize {
    let mut num = 0;
    let mut fixed = vec![vec![]];
    let n = g.order();
    for i in orbits(&g, &fixed) {
        fixed[0].push(i);
        for j in orbits(&g, &fixed) {
            if i < j && g.is_edge(i, j) {
                num += 1;
            }
        }
        fixed[0].pop();
    }
    num
}

fn naive_rotation(g: &GraphNauty) -> usize {
    let mut num = 0;
    let n = g.order();
    for i in 0..n {
        for j in 0..n {
            if i != j && g.is_edge(i, j) {
                for k in 0..n {
                    if k != i && k != j && !g.is_edge(i, k) {
                        num += 1;
                    }
                }
            }
        }
    }
    num
}

fn orbits_rotation(g: &GraphNauty) -> usize {
    let mut num = 0;
    let mut fixed = vec![vec![], vec![]];
    let n = g.order();
    for i in orbits(&g, &fixed) {
        fixed[0].push(i);
        for j in orbits(&g, &fixed) {
            fixed[1].push(j);
            if i != j && g.is_edge(i, j) {
                for k in orbits(&g, &fixed) {
                    if k != i && k != j && !g.is_edge(i, k) {
                        num += 1;
                    }
                }
            }
            fixed[1].pop();
        }
        fixed[0].pop();
    }
    num
}

fn run_experiment<F>(f: F, name: &str, filtering: bool)
    where F: Fn(&GraphNauty) -> usize
{
    let start = Instant::now();
    let total: usize = GRAPHS6
        .iter()
        .map(|x| from_g6::<GraphNauty>(x).unwrap())
        .map(|x| f(&x))
        .sum();
    let end = start.elapsed();
    println!(
        "Number of {} found {} filtering automorphisms: {}",
        name,
        if filtering {"with"} else {"without"},
        total
    );
    println!("Time to compute them: {}ms", end.as_millis());
}

fn main() {
    run_experiment(naive_edges, "edges", false);
    run_experiment(orbits_edges, "edges", true);
    run_experiment(naive_rotation, "rotations", false);
    run_experiment(orbits_rotation, "rotations", true);
}
