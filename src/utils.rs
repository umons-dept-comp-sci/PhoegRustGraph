// [TODO]: Find a better name for this module

use std::collections::{HashMap, HashSet};
use std::fmt;
use ::Graph;
use ::nauty;

struct VF2Data<'a> {
    g1: &'a Graph,
    g2: &'a Graph,
    depth: usize,
    null: usize,
    num_out: usize,
    // Set of vertices already mapped.
    core_1: &'a mut Vec<usize>,
    core_2: &'a mut Vec<usize>,
    adj_1: &'a mut Vec<usize>,
    adj_2: &'a mut Vec<usize>,
    orbits: &'a Vec<usize>,
    taboo: &'a mut HashMap<usize, HashSet<usize>>,
}

impl<'a> fmt::Display for VF2Data<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "g1 : {}", self.g1)?;
        writeln!(f, "g2 : {}", self.g2)?;
        writeln!(f, "depth : {}", self.depth)?;
        writeln!(f, "null : {}", self.null)?;
        writeln!(f, "num_out : {:?}", self.num_out)?;
        writeln!(f, "core_1 : {:?}", self.core_1)?;
        writeln!(f, "core_2 : {:?}", self.core_2)?;
        writeln!(f, "adj_1 : {:?}", self.adj_1)?;
        writeln!(f, "adj_2 : {:?}", self.adj_2)?;
        writeln!(f, "orbits : {:?}", self.orbits)?;
        writeln!(f, "taboo : {:?}", self.taboo)
    }
}

fn vf2_rec(data: &mut VF2Data) -> Vec<Vec<usize>> {
    let mut res = Vec::new();
    if data.num_out == 0 {
        // println!("{}", data);
        // println!("MATCH\n\n");
        let mut mat = Vec::new();
        for (i, _) in data.core_1.iter().enumerate().filter(|&(_, &y)| y != data.null) {
            mat.push(i);
        }
        res.push(mat);
    } else {
        let p = data.compute_pairs();
        for (n, m) in p {
            // println!("{}", data);
            // print!("Pair ({},{}) : ", n, m);
            if data.filter(n, m) {
                // println!("ADDED\n\n");
                data.add_pair(n, m);
                res.extend(vf2_rec(data));
                data.remove_pair(n, m);
            } else {
                // println!("REFUSED\n\n");
            }
        }
    }
    res
}

/// Checks wether g2 is a subgraph of g1.
pub fn vf2(g1: &Graph, g2: &Graph) -> Vec<Vec<usize>> {
    assert!(g1.order() >= g2.order());
    let null = g1.order() + 1;
    let mut data = VF2Data {
        g1: g1,
        g2: g2,
        depth: 1,
        null: null,
        num_out: g2.order(),
        core_1: &mut vec![null; g1.order()],
        core_2: &mut vec![null; g2.order()],
        adj_1: &mut vec![0; g1.order()],
        adj_2: &mut vec![0; g2.order()],
        orbits: &nauty::canon_graph_fixed(&g2, &[]).2,
        taboo: &mut HashMap::new(),
    };
    // println!("orbits : {:?}", data.orbits);
    vf2_rec(&mut data)
}

impl<'a> VF2Data<'a> {
    fn add_pair(&mut self, n: usize, m: usize) {
        self.depth += 1;
        self.core_1[n] = m;
        self.core_2[m] = n;
        for i in self.g1.nodes_iter() {
            if (self.g1.is_edge(n, i) || i == n) && self.adj_1[i] == 0 {
                self.adj_1[i] = self.depth;
            }
        }
        let m_orbit = self.orbits[m];
        for i in self.g2.nodes_iter() {
            if (self.g2.is_edge(m, i) || i == m) && self.adj_2[i] == 0 {
                self.adj_2[i] = self.depth;
            }
            if i > m && self.orbits[i] == m_orbit {
                if !self.taboo.contains_key(&n) {
                    self.taboo.insert(n, HashSet::new());
                }
                self.taboo.get_mut(&n).unwrap().insert(i);
            }
        }
        self.num_out -= 1;
    }

    fn remove_pair(&mut self, n: usize, m: usize) {
        self.core_1[n] = self.null;
        self.core_2[m] = self.null;
        for i in self.g1.nodes_iter() {
            if self.adj_1[i] == self.depth {
                self.adj_1[i] = 0;
            }
        }
        for i in self.g2.nodes_iter() {
            if self.adj_2[i] == self.depth {
                self.adj_2[i] = 0;
            }
        }
        self.depth -= 1;
        self.num_out += 1;
    }

    fn filter(&self, n: usize, m: usize) -> bool {
        if self.taboo.contains_key(&n) && self.taboo.get(&n).unwrap().contains(&m) {
            return false;
        }
        for (n1, n2) in self.g1
            .nodes_iter()
            .filter(|&x| self.core_1[x] != self.null)
            .map(|x| (x, self.core_1[x])) {
            let (e1, e2) = (self.g1.is_edge(n, n1), self.g2.is_edge(m, n2));
            if e1 || e2 {
                if e1 != e2 {
                    return false;
                }
            }
        }
        // e num of edges out of core and adj, n num of edges out of core and in adj
        let (mut e1, mut n1, mut e2, mut n2) = (0, 0, 0, 0);
        for i in self.g1.nodes_iter().filter(|&x| self.core_1[x] == self.null) {
            if self.g1.is_edge(n, i) {
                if self.adj_1[i] > 0 {
                    n1 += 1;
                } else {
                    e1 += 1;
                }
            }
        }
        // [TODO]: Can we write this and avoid duplicated code ? adj_1 and adj_2 are not the same
        // type.
        for i in self.g2.nodes_iter().filter(|&x| self.core_2[x] == self.null) {
            if self.g2.is_edge(n, i) {
                if self.adj_2[i] > 0 {
                    n2 += 1;
                } else {
                    e2 += 1;
                }
            }
        }
        n2 <= n1 && e2 <= e1
    }

    fn compute_pairs(&self) -> Vec<(usize, usize)> {
        let adj_out =
            self.g1.nodes_iter().filter(|&x| self.core_1[x] == self.null && self.adj_1[x] > 0);
        let adj_min = self.g2
            .nodes_iter()
            .filter(|&x| self.core_2[x] == self.null && self.adj_2[x] > 0)
            .min();
        let adj_iter: Vec<(usize, usize)> = adj_out.zip(adj_min.iter().cloned().cycle()).collect();
        if !adj_iter.is_empty() {
            adj_iter
        } else {
            let out = self.g1.nodes_iter().filter(|&x| self.adj_1[x] == 0);
            let min = self.g2.nodes_iter().filter(|&x| self.adj_2[x] == 0).min();
            let out_iter = out.zip(min.iter().cloned().cycle()).collect();
            out_iter
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test_vf2_graph(g1: &Graph, g2: &Graph) {
        let matches = vf2(&g1, &g2);
        for t in matches {
            println!("{:?}", t);
        }
    }

    #[test]
    fn test_vf2() {
        let mut g1 = Graph::new(5);
        g1.add_edge(0, 1);
        g1.add_edge(1, 2);
        g1.add_edge(1, 3);
        g1.add_edge(1, 4);
        g1.add_edge(4, 2);
        g1.add_edge(4, 3);
        let mut g2 = Graph::new(3);
        g2.add_edge(0, 1);
        g2.add_edge(1, 2);
        g2.add_edge(2, 0);
        test_vf2_graph(&g1, &g2);
        g2 = Graph::new(2);
        g2.add_edge(0, 1);
        test_vf2_graph(&g1, &g2);
        g1 = Graph::new(7);
        for i in g1.nodes_iter().skip(1) {
            for j in g1.nodes_iter().take(i) {
                g1.add_edge(i, j);
            }
        }
        g2 = Graph::new(4);
        for i in g2.nodes_iter().skip(1) {
            for j in g2.nodes_iter().take(i) {
                g2.add_edge(j, i);
            }
        }
        test_vf2_graph(&g1, &g2);
        panic!();
    }
}
