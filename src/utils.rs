// [TODO]: Find a better name for this module

use std::collections::{HashMap, HashSet, BTreeSet, BTreeMap};
use std::fmt;
use ::Graph;

struct VF2Data<'a> {
    g1: &'a Graph,
    g2: &'a Graph,
    depth: usize,
    // Set of vertices already mapped.
    core_1: &'a mut HashMap<usize, usize>,
    core_2: &'a mut HashMap<usize, usize>,
    // Set of vertices outside of core. Allows iteration over them as well as adding and removing in
    // "constant" time.
    out_1: &'a mut HashSet<usize>,
    // BTreeSet allows adding, iteration, removing and getting the minimum with better complexity
    // than linear (more or less logarithmic).
    out_2: &'a mut BTreeSet<usize>,
    // Set of vertices adjacent to vertices in the core.
    adj_1: &'a mut HashMap<usize, usize>,
    adj_2: &'a mut BTreeMap<usize, usize>,
}

impl<'a> fmt::Display for VF2Data<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "depth : {:?}\n", self.depth)?;
        writeln!(f, "g1 : {:?}\n", self.g1)?;
        writeln!(f, "g2 : {:?}\n", self.g2)?;
        writeln!(f, "core_1 : {:?}\n", self.core_1)?;
        writeln!(f, "core_2 : {:?}\n", self.core_2)?;
        writeln!(f, "out_1 : {:?}\n", self.out_1)?;
        writeln!(f, "out_2 : {:?}\n", self.out_2)?;
        writeln!(f, "adj_1 : {:?}\n", self.adj_1)?;
        writeln!(f, "adj_2 : {:?}\n", self.adj_2)
    }
}

impl<'a> VF2Data<'a> {
    fn add_pair(&mut self, n: usize, m: usize, adj: bool) -> (usize, usize) {
        self.out_1.remove(&n);
        self.out_2.remove(&m);
        let (mut p1, mut p2) = (0, 0);
        if adj {
            p1 = self.adj_1.remove(&n).unwrap();
            p2 = self.adj_2.remove(&m).unwrap();
        }
        self.core_1.insert(n, m);
        self.core_2.insert(m, n);
        for i in self.g1.nodes_iter() {
            if self.g1.is_edge(i, n) && !self.core_1.contains_key(&i) &&
               !self.adj_1.contains_key(&i) {
                self.adj_1.insert(i, self.depth);
            }
        }
        for i in self.g2.nodes_iter() {
            if self.g2.is_edge(i, m) && !self.core_2.contains_key(&i) &&
               !self.adj_2.contains_key(&i) {
                self.adj_2.insert(i, self.depth);
            }
        }
        self.depth += 1;
        (p1, p2)
    }
    fn remove_pair(&mut self, n: usize, m: usize, adj: bool, p1: usize, p2: usize) {
        self.depth -= 1;
        self.out_1.insert(n);
        self.out_2.insert(m);
        if adj {
            self.adj_2.insert(m, p1);
            self.adj_1.insert(n, p2);
        }
        self.core_1.remove(&n);
        self.core_2.remove(&m);
        for i in self.g1.nodes_iter() {
            if self.g1.is_edge(i, n) && !self.core_1.contains_key(&i) &&
               self.adj_1.get(&i).unwrap() == &self.depth {
                self.adj_1.remove(&i);
            }
        }
        for i in self.g2.nodes_iter() {
            if self.g2.is_edge(i, m) && !self.core_2.contains_key(&i) &&
               self.adj_2.get(&i).unwrap() == &self.depth {
                self.adj_2.remove(&i);
            }
        }
    }

    fn filter(&self, n: usize, m: usize) -> bool {
        let mut match_neighbors = false;
        for (&n1, &n2) in self.core_1.iter() {
            let (e1, e2) = (self.g1.is_edge(n, n1), self.g2.is_edge(m, n2));
            if e1 || e2 {
                match_neighbors = true;
                if e1 != e2 {
                    return false;
                }
            }
        }
        if match_neighbors {
            true
        } else {
            // e num of edges out of core and adj, n num of edges out of core and in adj
            let (mut e1, mut n1, mut e2, mut n2) = (0, 0, 0, 0);
            for &i in self.out_1.iter() {
                if self.g1.is_edge(n, i) {
                    if self.adj_1.contains_key(&i) {
                        n1 += 1;
                    } else {
                        e1 += 1;
                    }
                }
            }
            // [TODO]: Can we write this and avoid duplicated code ? adj_1 and adj_2 are not the same
            // type.
            for &i in self.out_2.iter() {
                if self.g2.is_edge(n, i) {
                    if self.adj_2.contains_key(&i) {
                        n2 += 1;
                    } else {
                        e2 += 1;
                    }
                }
            }
            n2 <= n1 && e2 <= e1
        }
    }

    fn compute_pairs(&self) -> (Vec<(usize, usize)>, bool) {
        if !self.adj_1.is_empty() && !self.adj_2.is_empty() {
            let adj_iter = self.adj_1.keys().cloned();
            let min = self.adj_2.keys().take(1).cycle().cloned();
            (adj_iter.zip(min).collect(), true)
        } else {
            let out_iter = self.out_1.iter().cloned();
            let min = self.out_2.iter().take(1).cycle().cloned();
            (out_iter.zip(min).collect(), false)
        }
    }
}

fn vf2_rec(data: &mut VF2Data) {
    if data.out_2.is_empty() {
        // [TODO]: How to output the matches ?
        println!("Found a match");
        println!("{:?}", data.core_1);
    } else {
        let (p, adj) = data.compute_pairs();
        for (n, m) in p {
            if data.filter(n, m) {
                let (p1, p2) = data.add_pair(n, m, adj);
                vf2_rec(data);
                data.remove_pair(n, m, adj, p1, p2);
            }
        }
    }
}

/// Checks wether g2 is a subgraph of g1.
pub fn vf2(g1: &Graph, g2: &Graph) {
    assert!(g1.order() >= g2.order());
    let mut data = VF2Data {
        g1: g1,
        g2: g2,
        depth: 0,
        core_1: &mut HashMap::with_capacity(g2.order()),
        core_2: &mut HashMap::with_capacity(g2.order()),
        out_1: &mut HashSet::with_capacity(g1.order()),
        out_2: &mut BTreeSet::new(),
        adj_1: &mut HashMap::new(),
        adj_2: &mut BTreeMap::new(),
    };
    for i in g1.nodes_iter() {
        data.out_1.insert(i);
    }
    for i in g2.nodes_iter() {
        data.out_2.insert(i);
    }
    vf2_rec(&mut data)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_vf2() {
        let mut g1 = Graph::new(5);
        g1.add_edge(0, 1);
        g1.add_edge(0, 2);
        g1.add_edge(0, 3);
        g1.add_edge(3, 1);
        g1.add_edge(3, 2);
        let mut g2 = Graph::new(3);
        g2.add_edge(0, 1);
        g2.add_edge(1, 2);
        g2.add_edge(2, 0);
        vf2(&g1, &g2);
        panic!();
    }
}
