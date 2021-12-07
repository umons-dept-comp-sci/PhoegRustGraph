//! Module containing algorithms to compute the occurences of an induced subgraph in a bigger graph.
use crate::nauty;
use crate::Graph;
use crate::GraphIter;
use crate::GraphNauty;
use std::collections::{HashMap, HashSet};
use std::fmt;

trait VF2Data {
    /// Checks if the partial mapping is a full matching of a subgraph.
    fn is_full_match(&self) -> bool;
    /// Returns the list of vertices of the bigger graph that are part of the mapping. e.g., the
    /// vertices forming a cycle if the subgraph we were looking for is a cycle.
    fn get_match(&self) -> Vec<u64>;
    /// Adds a pair to the partial mapping.
    fn add_pair(&mut self, n: u64, m: u64);
    /// Removes a pair from the partial mapping. np and mp are n and m depth where they were added
    /// to the neighborhood or 0 if they were nover added.
    fn remove_pair(&mut self, n: u64, m: u64, np: u64, mp: u64);
    /// Checks whether adding the pair to the partial mapping could lead to a full match.
    fn filter(&self, n: u64, m: u64) -> bool;
    /// Computes the candidate pairs to consider.
    fn compute_pairs(&self) -> Vec<(u64, u64)>;
    /// Returns the current depth at which a vertex of G1 was added to the mapping or to the neighborhood
    /// of the mapping.
    fn get_vertex_depth_G1(&self, n: u64) -> u64;
    /// Returns the current depth at which a vertex of G2 was added to the mapping or to the neighborhood
    /// of the mapping.
    fn get_vertex_depth_G2(&self, n: u64) -> u64;
}

#[repr(C)]
struct VF2DataImpl<'a> {
    // The graph where we are looking for matchings.
    g1: &'a GraphNauty,
    // The graph we are trying to map onto g1.
    g2: &'a GraphNauty,
    // Current depth of the recursion. This is also the number of mapped vertices.
    depth: u64,
    // The value to use as a null value.
    null: u64,
    // Set of vertices already mapped. The nth value is the number of the vertex of g2 mapped to
    // the vertex n of g1 or the null value if it is not mapped.
    core_1: Vec<u64>,
    // Set of vertices already mapped. The nth value is the number of the vertex of g1 mapped to
    // the vertex n of g2 or the null value if it is not mapped.
    core_2: Vec<u64>,
    // The depth at which the nth vertex was added to the adjacency of the mapping in G1 or to the
    // mapping itself.
    adj_1: Vec<u64>,
    // The depth at which the nth vertex was added to the adjacency of the mapping in G2 or to the
    // mapping itself.
    adj_2: Vec<u64>,
    // The orbits of the automorphism group of G2. The nth entry is the number of the lowest node
    // in the same orbit as the node n.
    orbits: Vec<u64>,
    // For each vertex, we ban exploring vertices in the same orbit as mapping to the same node of
    // G1 as it would be symmetrical.
    taboo: HashMap<u64, HashSet<u64>>,
}

impl<'a> fmt::Display for VF2DataImpl<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "g1 : {}", self.g1)?;
        writeln!(f, "g2 : {}", self.g2)?;
        writeln!(f, "depth : {}", self.depth)?;
        writeln!(f, "null : {}", self.null)?;
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
pub fn subgraphs<'a>(
    g1: &'a GraphNauty,
    g2: &'a GraphNauty,
) -> impl Iterator<Item = Vec<u64>> + 'a {
    SubgraphIter::without_orbits(g1, g2)
}

impl<'a> VF2Data for VF2DataImpl<'a> {
    fn is_full_match(&self) -> bool {
        self.depth == self.g2.order() + 1
    }

    fn get_match(&self) -> Vec<u64> {
        self.core_1
            .iter()
            .enumerate()
            .filter_map(|(x, &y)| if y != self.null { Some(x as u64) } else { None })
            .collect()
    }

    fn add_pair(&mut self, n: u64, m: u64) {
        self.depth += 1;
        // Adding the mapping to the partial mapping
        self.core_1[n as usize] = m;
        self.core_2[m as usize] = n;
        // Updating values for vertices in G1. If it was not already adjacent to a vertex in the
        // mapping, we set the value depth and we also set the value for n to the depth. This
        // makes restoring the state when removing n from the mapping easier.
        for i in self.g1.neighbors(n).chain(Some(n).iter().cloned()) {
            if self.adj_1[i as usize] == 0 {
                self.adj_1[i as usize] = self.depth;
            }
        }
        let m_orbit = self.orbits[m as usize];
        for i in self.g2.vertices() {
            // Update adj_2 the same way as before.
            if (self.g2.is_edge(m, i) || i == m) && self.adj_2[i as usize] == 0 {
                self.adj_2[i as usize] = self.depth;
            }
            // If a vertex has higher number than m and is in the same orbit, we forbid mapping n
            // and i since it would be symmetrical to mapping m and n.
            if i > m && self.orbits[i as usize] == m_orbit {
                self.taboo.entry(n).or_default().insert(i);
            }
        }
    }

    fn remove_pair(&mut self, n: u64, m: u64, np: u64, mp: u64) {
        //  We remove the mapping.
        self.core_1[n as usize] = self.null;
        self.core_2[m as usize] = self.null;
        // Every vertex of G1 added as neighbor of a mapped vertex at this depth is no longer
        // adjacent to a mapped vertex as it was adjacent to n.
        for i in self.g1.vertices() {
            if self.adj_1[i as usize] == self.depth {
                self.adj_1[i as usize] = 0;
            }
        }
        self.adj_1[n as usize] = np;
        // Same as before but for G2.
        for i in self.g2.vertices() {
            if self.adj_2[i as usize] == self.depth {
                self.adj_2[i as usize] = 0;
            }
        }
        self.adj_1[m as usize] = mp;
        // The depth decreases.
        self.depth -= 1;
    }

    fn filter(&self, n: u64, m: u64) -> bool {
        // We do not allow mapping n with a vertex in the same orbit as an already tried vertex of
        // G2.
        if self.taboo.contains_key(&n) && self.taboo[&n].contains(&m) {
            return false;
        }
        // The edges between mapped vertices should correspond. i.e., if x and y are adjacent in
        // G2, their mapped vertices in G1 should also be adjacent.
        for (n1, n2) in self
            .g1
            .vertices()
            .filter(|&x| self.core_1[x as usize] != self.null)
            .map(|x| (x, self.core_1[x as usize]))
        {
            let (e1, e2) = (self.g1.is_edge(n, n1), self.g2.is_edge(m, n2));
            if e1 != e2 {
                return false;
            }
        }
        // e num of edges out of core and adj, n num of edges out of core and in adj
        let (mut e1, mut n1, mut e2, mut n2) = (0, 0, 0, 0);
        for i in self
            .g1
            .neighbors(n)
            .filter(|&x| self.core_1[x as usize] == self.null)
        {
            if self.adj_1[i as usize] > 0 {
                n1 += 1;
            } else {
                e1 += 1;
            }
        }
        // [TODO]: Can we write this and avoid duplicated code ? adj_1 and adj_2 are not the same
        // type.
        for i in self
            .g2
            .neighbors(m)
            .filter(|&x| self.core_2[x as usize] == self.null)
        {
            if self.adj_2[i as usize] > 0 {
                n2 += 1;
            } else {
                e2 += 1;
            }
        }
        n2 <= n1 && e2 <= e1
    }

    fn compute_pairs(&self) -> Vec<(u64, u64)> {
        self.compute_pairs_internal(&self.g1.vertices().collect::<Vec<_>>().as_slice())
    }

    fn get_vertex_depth_G1(&self, n: u64) -> u64 {
        self.adj_1[n as usize]
    }

    fn get_vertex_depth_G2(&self, n: u64) -> u64 {
        self.adj_2[n as usize]
    }
}

impl<'a> VF2DataImpl<'a> {
    fn new(graph1: &'a GraphNauty, graph2: &'a GraphNauty) -> VF2DataImpl<'a> {
        assert!(graph1.order() >= graph2.order());
        let nullv = graph1.order() + 1;
        VF2DataImpl {
            g1: graph1,
            g2: graph2,
            depth: 1,
            null: nullv,
            core_1: vec![nullv; graph1.order() as usize],
            core_2: vec![nullv; graph2.order() as usize],
            adj_1: vec![0; graph1.order() as usize],
            adj_2: vec![0; graph2.order() as usize],
            orbits: nauty::canon_graph_fixed(&graph2, &[]).2,
            taboo: HashMap::new(),
        }
    }
    fn compute_pairs_internal(&self, g1_nodes: &[u64]) -> Vec<(u64, u64)> {
        let adj_out = g1_nodes
            .iter()
            .filter(|&&x| self.core_1[x as usize] == self.null && self.adj_1[x as usize] > 0)
            .cloned();
        let adj_min = self
            .g2
            .vertices()
            .filter(|&x| self.core_2[x as usize] == self.null && self.adj_2[x as usize] > 0)
            .min();
        let adj_iter: Vec<(u64, u64)> = adj_out.zip(adj_min.iter().cloned().cycle()).collect();
        if !adj_iter.is_empty() {
            adj_iter
        } else {
            let out = g1_nodes
                .iter()
                .filter(|&&x| self.adj_1[x as usize] == 0)
                .cloned();
            let min = self
                .g2
                .vertices()
                .filter(|&x| self.adj_2[x as usize] == 0)
                .min();
            out.zip(min.iter().cloned().cycle()).collect()
        }
    }
}

#[repr(C)]
struct VF2DataOrb<'a> {
    data: VF2DataImpl<'a>,
    fixed: Vec<Vec<u64>>,
    // The orbits of the automorphism group of G1. The nth entry is the number of the lowest node
    // in the same orbit as the node n.
    orbits: Vec<u64>,
    // For each vertex, we ban exploring vertices in the same orbit as mapping to the same node of
    // G2 as it would be symmetrical.
    taboo: HashMap<u64, HashSet<u64>>,
}

/// Returns every non-isomorphic occurrence of the graph `g2` in the graph `g1`.
pub fn subgraphs_orbits<'a>(
    g1: &'a GraphNauty,
    g2: &'a GraphNauty,
) -> impl Iterator<Item = Vec<u64>> + 'a {
    SubgraphIter::new(g1, g2)
}

impl<'a> VF2DataOrb<'a> {
    fn new(g1: &'a GraphNauty, g2: &'a GraphNauty) -> VF2DataOrb<'a> {
        let dataobj: VF2DataImpl<'a> = VF2DataImpl::new(g1, g2);
        let mut fixedempt = Vec::new();
        fixedempt.push(Vec::new());
        VF2DataOrb {
            data: dataobj,
            fixed: fixedempt,
            orbits: nauty::canon_graph_fixed(&g1, &[]).2,
            taboo: HashMap::new(),
        }
    }
}

impl<'a> fmt::Display for VF2DataOrb<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.data)?;
        writeln!(f, "fixed : {:?}", self.fixed)?;
        writeln!(f, "orbits : {:?}", self.orbits)?;
        writeln!(f, "taboo : {:?}", self.taboo)
    }
}

impl<'a> VF2Data for VF2DataOrb<'a> {
    fn is_full_match(&self) -> bool {
        self.data.is_full_match()
    }

    fn get_match(&self) -> Vec<u64> {
        self.data.get_match()
    }

    fn add_pair(&mut self, n: u64, m: u64) {
        self.data.add_pair(n, m);
        let n_orbit = self.orbits[n as usize];
        for i in self.data.g1.vertices() {
            // If a vertex has higher number than m and is in the same orbit, we forbid mapping n
            // and i since it would be symmetrical to mapping m and n.
            if i > n && self.orbits[i as usize] == n_orbit {
                self.taboo.entry(m).or_default().insert(i);
            }
        }
        self.fixed[0].push(n);
    }

    fn remove_pair(&mut self, n: u64, m: u64, np: u64, mp: u64) {
        self.data.remove_pair(n, m, np, mp);
        self.fixed[0].pop();
    }

    fn filter(&self, n: u64, m: u64) -> bool {
        // We do not allow mapping n with a vertex in the same orbit as an already tried vertex of
        // G1.
        if self.taboo.contains_key(&m) && self.taboo[&m].contains(&n) {
            return false;
        }
        self.data.filter(n, m)
    }

    fn compute_pairs(&self) -> Vec<(u64, u64)> {
        self.data
            .compute_pairs_internal(&nauty::orbits(self.data.g1, self.fixed.as_slice()))
        //self.data.compute_pairs()
    }

    fn get_vertex_depth_G1(&self, n: u64) -> u64 {
        self.data.get_vertex_depth_G1(n)
    }

    fn get_vertex_depth_G2(&self, n: u64) -> u64 {
        self.data.get_vertex_depth_G2(n)
    }
}

#[derive(Debug)]
enum VF2Step {
    ADDING {
        n: u64,
        m: u64,
    },
    REMOVING {
        n: u64,
        m: u64,
        n_previous_depth: u64,
        m_previous_depth: u64,
    },
}

#[repr(C)]
struct SubgraphIter<D>
where
    D: VF2Data,
{
    data: D,
    queue: Vec<VF2Step>,
}

impl<'a> SubgraphIter<VF2DataImpl<'a>> {
    fn without_orbits(g1: &'a GraphNauty, g2: &'a GraphNauty) -> SubgraphIter<VF2DataImpl<'a>> {
        let data: VF2DataImpl<'a> = VF2DataImpl::new(g1, g2);
        SubgraphIter::init(data)
    }
}

impl<'a> SubgraphIter<VF2DataOrb<'a>> {
    fn new(g1: &'a GraphNauty, g2: &'a GraphNauty) -> SubgraphIter<VF2DataOrb<'a>> {
        let data: VF2DataOrb<'a> = VF2DataOrb::new(g1, g2);
        SubgraphIter::init(data)
    }
}

impl<'a, D> SubgraphIter<D>
where
    D: VF2Data,
{
    fn init(dataobj: D) -> SubgraphIter<D> {
        let mut iter = SubgraphIter {
            data: dataobj,
            queue: Vec::new(),
        };
        // Computes the possible matching that can be added.
        let p = iter.data.compute_pairs();
        for (n, m) in p {
            // Check if this matching could work.
            if iter.data.filter(n, m) {
                iter.queue.push(VF2Step::ADDING { n: n, m: m });
            }
        }
        iter
    }
}

impl<'a, D> Iterator for SubgraphIter<D>
where
    D: VF2Data,
{
    type Item = Vec<u64>;

    // The VF2 algorithm works by exploring mappings between the vertices of the subgraph and
    // vertices of the graph. It is normally a recursive algorithm that we implemented as iterative
    // using a queue. This way, we do not need to allocate as much graphs. Each step in the queue
    // corresponds to a mapping between a vertex of G1 and a vertex of G2 that we either need to
    // add to the partial mapping we have and check if it is a subgraph matching or to remove this
    // pair because we already explored all mappings with this pair.
    fn next(&mut self) -> Option<Vec<u64>> {
        let mut found = false;
        let mut res = None;
        // While we haven't found a matching of the subgraph and we still have mappings to
        // explore.
        while !found && !self.queue.is_empty() {
            //println!("{:?}", self.queue);
            // We take the next pair to try.
            let step = self.queue.pop().unwrap();
            // If this pair is to be removed to the partial mapping, we remove it.
            // This is to restore the state after exploring all mappings with this pair.
            if let VF2Step::REMOVING {
                n,
                m,
                n_previous_depth,
                m_previous_depth,
            } = step
            {
                self.data.remove_pair(n, m, n_previous_depth, m_previous_depth);
            } else if let VF2Step::ADDING { n, m } = step {
                // We add a step to remove this pair from the partial mapping once we're done
                // exploring.
                self.queue.push(VF2Step::REMOVING {
                    n: n,
                    m: m,
                    n_previous_depth: self.data.get_vertex_depth_G1(n),
                    m_previous_depth: self.data.get_vertex_depth_G2(m),
                });
                // We add the pair to our partial mapping.
                self.data.add_pair(n, m);
                // If we found a full match, we output it as a subgraph matching.
                if self.data.is_full_match() {
                    found = true;
                    res = Some(self.data.get_match());
                    //println!("FOUND {:?}", res);
                } else {
                    // If we did not find a full match, we compute the possible pairs that can be
                    // added to our partial mapping.
                    let p = self.data.compute_pairs();
                    for (n, m) in p {
                        // For each pair, if adding it might lead to a partial mapping, we queue
                        // it.
                        if self.data.filter(n, m) {
                            self.queue.push(VF2Step::ADDING { n: n, m: m });
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

    fn apply_test_vf2<VF2>(matches: &mut Vec<Vec<u64>>, vf2: VF2)
    where
        VF2: Iterator<Item = Vec<u64>>,
    {
        let mut res: Vec<Vec<u64>> = vf2.collect();
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
    fn test_vf2_graph(g1: &GraphNauty, g2: &GraphNauty) {
        println!("-----------------");
        let mut matches: Vec<Vec<u64>> = subgraphs(&g1, &g2).collect();
        matches.iter_mut().for_each(|x| x.sort());
        matches.sort();
        for t in matches {
            println!("{:?}", t);
        }
        println!("-----------------");
        matches = subgraphs_orbits(&g1, &g2).collect();
        matches.iter_mut().for_each(|x| x.sort());
        matches.sort();
        for t in matches {
            println!("{:?}", t);
        }
        println!("-----------------");
    }

    #[test]
    fn visual_test() {
        let mut g1 = GraphNauty::new(6);
        g1.add_edge(0, 1);
        g1.add_edge(1, 2);
        g1.add_edge(2, 3);
        g1.add_edge(3, 4);
        g1.add_edge(4, 0);
        g1.add_edge(5, 0);
        let mut g2 = GraphNauty::new(3);
        g2.add_edge(0, 1);
        g2.add_edge(1, 2);
        test_vf2_graph(&g1, &g2);
    }

    //#[allow(dead_code)]
    #[test]
    fn test_vf2() {
        let mut g1 = GraphNauty::new(5);
        g1.add_edge(0, 1);
        g1.add_edge(1, 2);
        g1.add_edge(1, 3);
        g1.add_edge(1, 4);
        g1.add_edge(4, 2);
        g1.add_edge(4, 3);
        let mut g2 = GraphNauty::new(3);
        g2.add_edge(0, 1);
        g2.add_edge(1, 2);
        g2.add_edge(2, 0);
        apply_test_vf2(&mut vec![vec![1, 2, 4], vec![1, 3, 4]], subgraphs(&g1, &g2));
        apply_test_vf2(&mut vec![vec![1, 2, 4]], subgraphs_orbits(&g1, &g2));
        g2 = GraphNauty::new(2);
        g2.add_edge(0, 1);
        apply_test_vf2(
            &mut vec![
                vec![0, 1],
                vec![1, 2],
                vec![1, 3],
                vec![1, 4],
                vec![2, 4],
                vec![3, 4],
            ],
            subgraphs(&g1, &g2),
        );
        apply_test_vf2(
            &mut vec![vec![0, 1], vec![1, 2], vec![1, 4], vec![2, 4]],
            subgraphs_orbits(&g1, &g2),
        );
        g1 = GraphNauty::new(9);
        for i in g1.vertices().skip(1).take(6) {
            for j in g1.vertices().take(i as usize) {
                g1.add_edge(i, j);
            }
        }
        g1.add_edge(4, 7);
        g1.add_edge(6, 8);
        g2 = GraphNauty::new(4);
        for i in g2.vertices().skip(1) {
            for j in g2.vertices().take(i as usize) {
                g2.add_edge(j, i);
            }
        }
        apply_test_vf2(
            &mut vec![
                vec![3, 4, 5, 6],
                vec![2, 4, 5, 6],
                vec![1, 4, 5, 6],
                vec![0, 4, 5, 6],
                vec![2, 3, 5, 6],
                vec![1, 3, 5, 6],
                vec![0, 3, 5, 6],
                vec![1, 2, 5, 6],
                vec![0, 2, 5, 6],
                vec![0, 1, 5, 6],
            ],
            subgraphs(&g1, &g2),
        );
        apply_test_vf2(
            &mut vec![vec![0, 1, 2, 3], vec![0, 1, 2, 4], vec![0, 1, 4, 6]],
            subgraphs_orbits(&g1, &g2),
        );
    }
}
