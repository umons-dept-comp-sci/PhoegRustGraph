//! Module containing algorithms to compute the occurences of an induced subgraph in a bigger graph.
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
    core_1: Vec<usize>,
    core_2: Vec<usize>,
    adj_1: Vec<usize>,
    adj_2: Vec<usize>,
    orbits: Vec<usize>,
    taboo: HashMap<usize, HashSet<usize>>,
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

/// Returns every occurence of the graph `g2` in the graph `g1` up to permutations among the orbits
/// of `g2`.
///
/// The graph `g2` must have at most the same order as `g1`.
pub fn subgraphs<'a>(g1: &'a Graph, g2: &'a Graph) -> impl Iterator<Item = Vec<usize>> + 'a {
    SubgraphIter::without_orbits(g1, g2)
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
    fn new(g1: &'a Graph, g2: &'a Graph) -> VF2DataImpl<'a> {
        assert!(g1.order() >= g2.order());
        let null = g1.order() + 1;
        VF2DataImpl {
            g1: g1,
            g2: g2,
            depth: 1,
            null: null,
            num_out: g2.order(),
            core_1: vec![null; g1.order()],
            core_2: vec![null; g2.order()],
            adj_1: vec![0; g1.order()],
            adj_2: vec![0; g2.order()],
            orbits: nauty::canon_graph_fixed(&g2, &[]).2,
            taboo: HashMap::new(),
        }
    }
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
    data: VF2DataImpl<'a>,
    fixed: Vec<Vec<u32>>,
}

/// Returns every non-isomorphic occurence of the graph `g2` in the graph `g1`.
pub fn subgraphs_orbits<'a>(g1: &'a Graph, g2: &'a Graph) -> impl Iterator<Item = Vec<usize>> + 'a {
    SubgraphIter::new(g1, g2)
}

impl<'a> VF2DataOrb<'a> {
    fn new(g1: &'a Graph, g2: &'a Graph) -> VF2DataOrb<'a> {
        let data: VF2DataImpl<'a> = VF2DataImpl::new(g1, g2);
        let fixed = Vec::new();
        VF2DataOrb {
            data: data,
            fixed: fixed,
        }
    }
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

struct SubgraphIter<D>
    where D: VF2Data
{
    data: D,
    queue: Vec<(usize, usize, bool)>,
}

impl<'a> SubgraphIter<VF2DataImpl<'a>> {
    fn without_orbits(g1: &'a Graph, g2: &'a Graph) -> SubgraphIter<VF2DataImpl<'a>> {
        let data: VF2DataImpl<'a> = VF2DataImpl::new(g1, g2);
        SubgraphIter::init(data)
    }
}

impl<'a> SubgraphIter<VF2DataOrb<'a>> {
    fn new(g1: &'a Graph, g2: &'a Graph) -> SubgraphIter<VF2DataOrb<'a>> {
        let data: VF2DataOrb<'a> = VF2DataOrb::new(g1, g2);
        SubgraphIter::init(data)
    }
}

impl<'a, D> SubgraphIter<D>
    where D: VF2Data
{
    fn init(data: D) -> SubgraphIter<D> {
        let mut iter = SubgraphIter {
            data: data,
            queue: Vec::new(),
        };
        let p = iter.data.compute_pairs();
        for (n, m) in p {
            if iter.data.filter(n, m) {
                iter.queue.push((n, m, true));
            }
        }
        iter
    }
}

impl<'a, D> Iterator for SubgraphIter<D>
    where D: VF2Data
{
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Vec<usize>> {
        let mut found = false;
        let mut res = None;
        while !found && !self.queue.is_empty() {
            let (n, m, add) = self.queue.pop().unwrap();
            if !add {
                self.data.remove_pair(n, m);
            } else {
                self.queue.push((n, m, false));
                self.data.add_pair(n, m);
                if self.data.is_full_match() {
                    found = true;
                    res = Some(self.data.get_match());
                } else {
                    let p = self.data.compute_pairs();
                    for (n, m) in p {
                        if self.data.filter(n, m) {
                            self.queue.push((n, m, true));
                        }
                    }
                }
            }
        }
        res
    }
}

#[cfg(test)]
mod testing {
    use super::*;

    fn apply_test_vf2<VF2>(matches: &mut Vec<Vec<usize>>, vf2: VF2)
        where VF2: Iterator<Item = Vec<usize>>
    {
        let mut res: Vec<Vec<usize>> = vf2.collect();
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
        let matches = subgraphs(&g1, &g2);
        for t in matches {
            println!("{:?}", t);
        }
        println!("-----------------");
        let matches = subgraphs_orbits(&g1, &g2);
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
        apply_test_vf2(&mut vec![vec![1, 2, 4], vec![1, 3, 4]], subgraphs(&g1, &g2));
        apply_test_vf2(&mut vec![vec![1, 2, 4]], subgraphs_orbits(&g1, &g2));
        g2 = Graph::new(2);
        g2.add_edge(0, 1);
        apply_test_vf2(&mut vec![vec![0, 1], vec![1, 2], vec![1, 3], vec![1, 4], vec![2, 4],
                                 vec![3, 4]],
                       subgraphs(&g1, &g2));
        apply_test_vf2(&mut vec![vec![0, 1], vec![1, 2], vec![1, 4], vec![2, 4]],
                       subgraphs_orbits(&g1, &g2));
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
        apply_test_vf2(&mut vec![vec![3, 4, 5, 6],
                                 vec![2, 4, 5, 6],
                                 vec![1, 4, 5, 6],
                                 vec![0, 4, 5, 6],
                                 vec![2, 3, 5, 6],
                                 vec![1, 3, 5, 6],
                                 vec![0, 3, 5, 6],
                                 vec![1, 2, 5, 6],
                                 vec![0, 2, 5, 6],
                                 vec![0, 1, 5, 6]],
                       subgraphs(&g1, &g2));
        apply_test_vf2(&mut vec![vec![0, 1, 2, 3], vec![0, 1, 2, 4], vec![0, 1, 4, 6]],
                       subgraphs_orbits(&g1, &g2));
    }
}
