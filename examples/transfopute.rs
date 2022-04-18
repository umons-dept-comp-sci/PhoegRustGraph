use graph::format::from_g6;
use graph::nauty::orbits;
use graph::subgraphs::{subgraphs, subgraphs_orbits, subgraphs_symm};
use graph::{Graph, GraphNauty};
use indicatif::{ProgressBar, ProgressIterator};
use std::fs::File;
use std::io::{Write, BufReader, BufRead};
use std::time::{Instant};

fn get_lines(n: u64) -> Vec<String> {
    let file = File::open(format!("g{}.g6", n)).unwrap();
    let lines: Vec<String> = BufReader::new(file)
        .lines()
        .map(|x| x.unwrap())
        .collect();
    lines
}

fn nomethod_k5(g: &GraphNauty) -> usize {
    let n = g.order();
    let mut count = 0;
    for a in 0..n - 4 {
        for b in a + 1..n - 3 {
            if g.is_edge(a, b) {
                for c in b + 1..n - 2 {
                    if g.is_edge(c, a) && g.is_edge(c, b) {
                        for d in c + 1..n - 1 {
                            if g.is_edge(d, a) && g.is_edge(d, b) && g.is_edge(d, c) {
                                for e in d + 1..n {
                                    if g.is_edge(e, a)
                                        && g.is_edge(e, b)
                                        && g.is_edge(e, c)
                                        && g.is_edge(e, d)
                                    {
                                        count += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    count
}

fn nomethod_p3(g: &GraphNauty) -> usize {
    let n = g.order();
    let mut count = 0;
    for u in 0..n {
        for v in 0..n {
            if v != u && g.is_edge(u, v) {
                for w in 0..n {
                    if w > u && w != v && g.is_edge(v, w) && !g.is_edge(u, w) {
                        count += 1;
                    }
                }
            }
        }
    }
    count
}

fn itermethod_p3(g: &GraphNauty) -> usize {
    let mut fixed = Vec::new();
    let n = g.order();
    let mut count = 0;
    for u in orbits(g, &fixed) {
        fixed.push(vec![u]);
        for v in orbits(g, &fixed) {
            if v != u && g.is_edge(u, v) {
                fixed.push(vec![v]);
                for w in orbits(g, &fixed) {
                    if w > u && w != v && g.is_edge(v, w) && !g.is_edge(u, w) {
                        count += 1;
                    }
                }
                fixed.pop();
            }
        }
        fixed.pop();
    }
    count
}

fn itermethod_k5(g: &GraphNauty) -> usize {
    let n = g.order();
    let mut count = 0;
    let mut fixed = vec![vec![]];
    for a in orbits(g, &fixed) {
        fixed[0].push(a);
        for b in orbits(g, &fixed) {
            if a < b && g.is_edge(a, b) {
                fixed[0].push(b);
                for c in orbits(g, &fixed) {
                    if b < c && g.is_edge(c, a) && g.is_edge(c, b) {
                        fixed[0].push(c);
                        for d in orbits(g, &fixed) {
                            if c < d && g.is_edge(d, a) && g.is_edge(d, b) && g.is_edge(d, c) {
                                fixed[0].push(d);
                                for e in orbits(g, &fixed) {
                                    if d < e
                                        && g.is_edge(e, a)
                                        && g.is_edge(e, b)
                                        && g.is_edge(e, c)
                                        && g.is_edge(e, d)
                                    {
                                        count += 1;
                                    }
                                }
                                fixed[0].pop();
                            }
                        }
                        fixed[0].pop();
                    }
                }
                fixed[0].pop();
            }
        }
        fixed[0].pop();
    }
    count
}

/// Adds a pendant vertex at the middle vertex of an induced path of size 2*k+1
/// using the iterating method.
fn vf2method_p(g: &GraphNauty, k: u64) -> usize {
    let pn = 2 * k + 1;
    let n = g.order();
    let mut h = GraphNauty::new(pn);
    for i in 0..pn - 1 {
        h.add_edge(i, i + 1);
    }
    subgraphs_orbits(g, &h).count()
}

fn vf2method_k(g: &GraphNauty, k: u64) -> usize {
    let n = g.order();
    let mut h = GraphNauty::new(k);
    for i in 0..k - 1 {
        for j in i + 1..k {
            h.add_edge(i, j);
        }
    }
    subgraphs_orbits(g, &h).count()
}

/// Adds a pendant vertex at the middle vertex of an induced path of size 2*k+1
/// using the iterating method.
fn hypermethod_p(g: &GraphNauty, k: u64) -> usize {
    let pn = 2 * k + 1;
    let n = g.order();
    let mut h = GraphNauty::new(pn);
    for i in 0..pn - 1 {
        h.add_edge(i, i + 1);
    }
    let mut hg = g.clone();
    let mut hn = n;
    let mut fixed = vec![vec![]];
    for sg in subgraphs_symm(g, &h) {
        hg.add_vertex();
        for v in sg {
            hg.add_edge(hn, v);
        }
        fixed[0].push(hn);
        hn += 1;
    }
    orbits(&hg, &fixed).iter().filter(|x| **x >= n).count()
}

fn hypermethod_k(g: &GraphNauty, k: u64) -> usize {
    let n = g.order();
    let mut h = GraphNauty::new(k);
    for i in 0..k - 1 {
        for j in i + 1..k {
            h.add_edge(i, j);
        }
    }
    let mut hg = g.clone();
    let mut hn = n;
    let mut fixed = vec![vec![]];
    for sg in subgraphs_symm(g, &h) {
        hg.add_vertex();
        for v in sg {
            hg.add_edge(hn, v);
        }
        fixed[0].push(hn);
        hn += 1;
    }
    orbits(&hg, &fixed).iter().filter(|x| **x >= n).count()
}

fn hypermethodcopy_p(g: &GraphNauty, k: u64) -> usize {
    let pn = 2*k+1;
    let n = g.order();
    let mut h = GraphNauty::new(pn);
    for i in 1..pn {
        h.add_edge(i, i-1);
    }
    let mut hg = g.clone();
    let mut hn = n;
    let mut fixed = vec![vec![]];
    for sg in subgraphs(g, &h) {
        hg.add_vertex();
        let mut p = 1;
        for v in &sg {
            hg.add_edge(hn, *v);
            hg.add_vertex();
            hg.add_edge(hn + p, *v);
            hg.add_edge(hn + p, hn);
            p += 1;
        }
        for i in 2..pn {
            hg.add_edge(hn+i, hn+i-1);
        }
        fixed[0].push(hn);
        hn += pn + 1;
    }
    orbits(&hg, &fixed)
        .iter()
        .filter(|x| **x >= n && (**x - n) % (pn + 1) == 0)
        .count()
}

fn hypermethodcopy_k(g: &GraphNauty, k: u64) -> usize {
    let n = g.order();
    let mut h = GraphNauty::new(k);
    for i in 0..k - 1 {
        for j in i + 1..k {
            h.add_edge(i, j);
        }
    }
    let mut hg = g.clone();
    let mut hn = n;
    let mut fixed = vec![vec![]];
    for sg in subgraphs(g, &h) {
        hg.add_vertex();
        let mut p = 1;
        for v in &sg {
            hg.add_edge(hn, *v);
            hg.add_vertex();
            hg.add_edge(hn + p, *v);
            hg.add_edge(hn + p, hn);
            p += 1;
        }
        for i in 1..k {
            for j in i + 1..=k {
                hg.add_edge(hn + i, hn + j);
            }
        }
        fixed[0].push(hn);
        hn += k + 1;
    }
    orbits(&hg, &fixed)
        .iter()
        .filter(|x| **x >= n && (**x - n) % (k + 1) == 0)
        .count()
}

fn try_method<M>(
    m: M,
    name: &str,
    lines: &[GraphNauty],
) -> (u64, u64)
where
    M: Fn(&GraphNauty) -> usize,
{
    eprintln!("\tmethod {}", name);
    let prog = ProgressBar::new(lines.len() as u64);
    prog.set_draw_rate(10);
    prog.enable_steady_tick(100);
    let now = Instant::now();
    let r: usize = lines.iter().progress_with(prog).map(|x| m(&x)).sum();
    let t = now.elapsed();
    eprintln!("\t\t {} found in {} ms", r, t.as_millis());
    (r as u64, t.as_millis() as u64)
}

fn run_test<M: ?Sized>(methods: &[Box<M>], names: &[&str], prefix: &str, minn: u64, maxn: u64)
where
    M: Fn(&GraphNauty) -> usize,
{
    let mut times = File::create(format!("{}-times.dat", prefix)).unwrap();
    write!(times, "n");
    for name in names.iter() {
        write!(times, " {}", name);
    }
    writeln!(times, "");
    let mut sizes = File::create(format!("{}-sizes.dat", prefix)).unwrap();
    write!(sizes, "n");
    for name in names.iter() {
        write!(sizes, " {}", name);
    }
    writeln!(sizes, "");
    let mut res;
    for n in minn..=maxn {
        eprintln!("n={}", n);
        let lines: Vec<GraphNauty> = get_lines(n)
            .iter()
            .map(|x| GraphNauty::parse_graph6(x))
            .collect();
        write!(sizes, "{}", n);
        write!(times, "{}", n);
        for (m, name) in methods.iter().zip(names) {
            res = try_method(m, name, &lines);
            write!(sizes, " {}", res.0);
            write!(times, " {}", res.1);
        }
        writeln!(sizes, "");
        writeln!(times, "");
    }
}

fn main() {
    run_test(
        &[
            Box::new(nomethod_p3) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(itermethod_p3) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(|x: &GraphNauty| vf2method_p(x, 1)) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(|x: &GraphNauty| hypermethod_p(x, 1)) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(|x: &GraphNauty| hypermethodcopy_p(x, 1)) as Box<dyn Fn(&GraphNauty) -> usize>,
        ],
        &["nofilt", "iter", "subgraph", "hyper", "hypercopy"],
        "p3",
        3,
        9,
    );
    run_test(
        &[
            Box::new(nomethod_k5) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(itermethod_k5) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(|x: &GraphNauty| vf2method_k(x, 5)) as Box<dyn Fn(&GraphNauty) -> usize>,
            Box::new(|x: &GraphNauty| hypermethod_k(x, 5)) as Box<dyn Fn(&GraphNauty) -> usize>,
        ],
        &["nofilt", "iter", "subgraph", "hyper"],
        "k5",
        5,
        9,
    );
}
