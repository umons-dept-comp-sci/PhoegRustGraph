// [TODO]: Find a better name for this module

use std::collections::{HashMap, HashSet};
use std::fmt;
use ::Graph;
use ::nauty;

trait VF2Data {
    fn is_full_match(&self) -> bool;
    fn get_match(&self) -> Vec<usize>;
    fn add_pair(&mut self, n: usize, m: usize);
    fn remove_pair(&mut self, n: usize, m: usize);
    fn filter(&self, n: usize, m: usize) -> bool;
    fn compute_pairs(&self) -> Vec<(usize, usize)>;
}

struct VF2DataImpl<'a> {
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

impl<'a> fmt::Display for VF2DataImpl<'a> {
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

fn vf2_rec<D>(data: &mut D) -> Vec<Vec<usize>>
    where D: VF2Data
{
    let mut res = Vec::new();
    if data.is_full_match() {
        // println!("MATCH");
        res.push(data.get_match());
    } else {
        let p = data.compute_pairs();
        for (n, m) in p {
            if data.filter(n, m) {
                data.add_pair(n, m);
                res.extend(vf2_rec(data));
                data.remove_pair(n, m);
            }
        }
    }
    res
}

/// Checks wether g2 is a subgraph of g1.
pub fn vf2(g1: &Graph, g2: &Graph) -> Vec<Vec<usize>> {
    assert!(g1.order() >= g2.order());
    let null = g1.order() + 1;
    let mut data = VF2DataImpl {
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

impl<'a> VF2Data for VF2DataImpl<'a> {
    fn is_full_match(&self) -> bool {
        self.num_out == 0
    }

    fn get_match(&self) -> Vec<usize> {
        self.core_1
            .iter()
            .enumerate()
            .filter_map(|(x, &y)| if y != self.null { Some(x) } else { None })
            .collect()
    }

    fn add_pair(&mut self, n: usize, m: usize) {
        self.depth += 1;
        self.core_1[n] = m;
        self.core_2[m] = n;
        for i in self.g1.neighbors(n).chain(Some(n).iter().cloned()) {
            if self.adj_1[i] == 0 {
                self.adj_1[i] = self.depth;
            }
        }
        let m_orbit = self.orbits[m];
        for i in self.g2.vertices() {
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
        // println!("n {}, m {}, taboo {:?}", n, m, self.taboo);
    }

    fn remove_pair(&mut self, n: usize, m: usize) {
        self.core_1[n] = self.null;
        self.core_2[m] = self.null;
        for i in self.g1.vertices() {
            if self.adj_1[i] == self.depth {
                self.adj_1[i] = 0;
            }
        }
        for i in self.g2.vertices() {
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
            .vertices()
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
        for i in self.g1.neighbors(n).filter(|&x| self.core_1[x] == self.null) {
            if self.adj_1[i] > 0 {
                n1 += 1;
            } else {
                e1 += 1;
            }
        }
        // [TODO]: Can we write this and avoid duplicated code ? adj_1 and adj_2 are not the same
        // type.
        for i in self.g2.neighbors(m).filter(|&x| self.core_2[x] == self.null) {
            if self.adj_2[i] > 0 {
                n2 += 1;
            } else {
                e2 += 1;
            }
        }
        n2 <= n1 && e2 <= e1
    }

    fn compute_pairs(&self) -> Vec<(usize, usize)> {
        self.compute_pairs_internal(&self.g1.vertices().collect())
    }
}

impl<'a> VF2DataImpl<'a> {
    fn compute_pairs_internal(&self, g1_nodes: &Vec<usize>) -> Vec<(usize, usize)> {
        let adj_out = g1_nodes.iter()
            .filter(|&&x| self.core_1[x] == self.null && self.adj_1[x] > 0)
            .cloned();
        let adj_min = self.g2
            .vertices()
            .filter(|&x| self.core_2[x] == self.null && self.adj_2[x] > 0)
            .min();
        let adj_iter: Vec<(usize, usize)> = adj_out.zip(adj_min.iter().cloned().cycle()).collect();
        if !adj_iter.is_empty() {
            adj_iter
        } else {
            let out = g1_nodes.iter().filter(|&&x| self.adj_1[x] == 0).cloned();
            let min = self.g2.vertices().filter(|&x| self.adj_2[x] == 0).min();
            let out_iter = out.zip(min.iter().cloned().cycle()).collect();
            out_iter
        }
    }
}

struct VF2DataOrb<'a> {
    data: &'a mut VF2DataImpl<'a>,
    fixed: &'a mut Vec<Vec<u32>>,
}

impl<'a> fmt::Display for VF2DataOrb<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.data)?;
        writeln!(f, "fixed : {:?}", self.fixed)
    }
}

impl<'a> VF2Data for VF2DataOrb<'a> {
    fn is_full_match(&self) -> bool {
        self.data.is_full_match()
    }

    fn get_match(&self) -> Vec<usize> {
        self.data.get_match()
    }

    fn add_pair(&mut self, n: usize, m: usize) {
        self.data.add_pair(n, m);
        self.fixed.push(vec![n as u32]);
    }

    fn remove_pair(&mut self, n: usize, m: usize) {
        self.data.remove_pair(n, m);
        self.fixed.pop();
    }

    fn filter(&self, n: usize, m: usize) -> bool {
        self.data.filter(n, m)
    }

    fn compute_pairs(&self) -> Vec<(usize, usize)> {
        self.data.compute_pairs_internal(&nauty::orbits(self.data.g1, self.fixed.as_slice()))
    }
}

pub fn vf2_orb(g1: &Graph, g2: &Graph) -> Vec<Vec<usize>> {
    assert!(g1.order() >= g2.order());
    let null = g1.order() + 1;
    let mut fixed = Vec::new();
    let mut data = VF2DataImpl {
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
    let mut data_orb = VF2DataOrb {
        fixed: &mut fixed,
        data: &mut data,
    };
    vf2_rec(&mut data_orb)
}

#[cfg(test)]
mod testing {
    use super::*;
    // use test::Bencher;

    fn apply_test_vf2<VF2>(g1: &Graph, g2: &Graph, matches: &mut Vec<Vec<usize>>, vf2: VF2)
        where VF2: Fn(&Graph, &Graph) -> Vec<Vec<usize>>
    {
        let mut res = vf2(g1, g2);
        assert_eq!(res.len(), matches.len());
        matches.iter_mut().for_each(|x| x.sort());
        matches.sort();
        res.iter_mut().for_each(|x| x.sort());
        res.sort();
        for (ref m, ref me) in res.iter().zip(matches.iter()) {
            assert_eq!(m.len(), me.len());
            for (n1, n2) in m.iter().zip(me.iter()) {
                assert_eq!(n1, n2);
            }
        }
    }

    #[allow(dead_code)]
    fn test_vf2_graph(g1: &Graph, g2: &Graph) {
        println!("-----------------");
        let matches = vf2(&g1, &g2);
        for t in matches {
            println!("{:?}", t);
        }
        println!("-----------------");
        let matches = vf2_orb(&g1, &g2);
        for t in matches {
            println!("{:?}", t);
        }
        println!("-----------------");
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
        apply_test_vf2(&g1, &g2, &mut vec![vec![1, 2, 4], vec![1, 3, 4]], vf2);
        apply_test_vf2(&g1, &g2, &mut vec![vec![1, 2, 4]], vf2_orb);
        g2 = Graph::new(2);
        g2.add_edge(0, 1);
        apply_test_vf2(&g1,
                       &g2,
                       &mut vec![vec![0, 1], vec![1, 2], vec![1, 3], vec![1, 4], vec![2, 4],
                                 vec![3, 4]],
                       vf2);
        apply_test_vf2(&g1,
                       &g2,
                       &mut vec![vec![0, 1], vec![1, 2], vec![1, 4], vec![2, 4]],
                       vf2_orb);
        g1 = Graph::new(9);
        for i in g1.vertices().skip(1).take(6) {
            for j in g1.vertices().take(i) {
                g1.add_edge(i, j);
            }
        }
        g1.add_edge(4, 7);
        g1.add_edge(6, 8);
        g2 = Graph::new(4);
        for i in g2.vertices().skip(1) {
            for j in g2.vertices().take(i) {
                g2.add_edge(j, i);
            }
        }
        apply_test_vf2(&g1,
                       &g2,
                       &mut vec![vec![0, 1, 2, 3],
                                 vec![0, 1, 2, 4],
                                 vec![0, 1, 2, 5],
                                 vec![0, 1, 2, 6],
                                 vec![0, 1, 3, 4],
                                 vec![0, 1, 3, 5],
                                 vec![0, 1, 3, 6],
                                 vec![0, 1, 4, 5],
                                 vec![0, 1, 4, 6],
                                 vec![0, 1, 5, 6]],
                       vf2);
        apply_test_vf2(&g1,
                       &g2,
                       &mut vec![vec![0, 1, 2, 3], vec![0, 1, 2, 4], vec![0, 1, 4, 6]],
                       vf2_orb);
    }

    //    #[bench]
    // fn bench_vf2_orbs(b: &mut Bencher) {
    // let mut g1 = Graph::new(5);
    // g1.add_edge(0, 1);
    // g1.add_edge(1, 2);
    // g1.add_edge(1, 3);
    // g1.add_edge(1, 4);
    // g1.add_edge(4, 2);
    // g1.add_edge(4, 3);
    // let mut g2 = Graph::new(3);
    // g2.add_edge(0, 1);
    // g2.add_edge(1, 2);
    // g2.add_edge(2, 0);
    // b.iter(|| vf2_orb(&g1, &g2));
    // g2 = Graph::new(2);
    // g2.add_edge(0, 1);
    // b.iter(|| vf2_orb(&g1, &g2));
    // g1 = Graph::new(7);
    // for i in g1.vertices().skip(1) {
    // for j in g1.vertices().take(i) {
    // g1.add_edge(i, j);
    // }
    // }
    // g2 = Graph::new(4);
    // for i in g2.vertices().skip(1) {
    // for j in g2.vertices().take(i) {
    // g2.add_edge(j, i);
    // }
    // }
    // b.iter(|| vf2_orb(&g1, &g2));
    // }
    //
    //
    // #[bench]
    // fn bench_vf2(b: &mut Bencher) {
    // let mut g1 = Graph::new(5);
    // g1.add_edge(0, 1);
    // g1.add_edge(1, 2);
    // g1.add_edge(1, 3);
    // g1.add_edge(1, 4);
    // g1.add_edge(4, 2);
    // g1.add_edge(4, 3);
    // let mut g2 = Graph::new(3);
    // g2.add_edge(0, 1);
    // g2.add_edge(1, 2);
    // g2.add_edge(2, 0);
    // b.iter(|| vf2(&g1, &g2));
    // g2 = Graph::new(2);
    // g2.add_edge(0, 1);
    // b.iter(|| vf2(&g1, &g2));
    // g1 = Graph::new(7);
    // for i in g1.vertices().skip(1) {
    // for j in g1.vertices().take(i) {
    // g1.add_edge(i, j);
    // }
    // }
    // g2 = Graph::new(3);
    // for i in g2.vertices().skip(1) {
    // for j in g2.vertices().take(i) {
    // g2.add_edge(j, i);
    // }
    // }
    // b.iter(|| vf2(&g1, &g2));
    //
    // }
}
