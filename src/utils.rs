// [TODO]: Find a better name for this module

use ::Graph;

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
}

fn vf2_rec(data: &mut VF2Data) {
    if data.num_out == 0 {
        // [TODO]: How to output the matches ?
        println!("Found a match");
        for (i, j) in data.core_1.iter().enumerate().filter(|&(x, &y)| y != data.null) {
            print!("{} : {}, ", i, j);
        }
        println!("");
    } else {
        let p = data.compute_pairs();
        for (n, m) in p {
            if data.filter(n, m) {
                data.add_pair(n, m);
                vf2_rec(data);
                data.remove_pair(n, m);
            }
        }
    }
}

/// Checks wether g2 is a subgraph of g1.
pub fn vf2(g1: &Graph, g2: &Graph) {
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
    };
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
        for i in self.g2.nodes_iter() {
            if (self.g2.is_edge(m, i) || i == m) && self.adj_2[i] == 0 {
                self.adj_2[i] = self.depth;
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
        let mut match_neighbors = false;
        for (n1, n2) in self.g1
            .nodes_iter()
            .filter(|&x| self.core_1[x] != self.null)
            .map(|x| (x, self.core_1[x])) {
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
        vf2(&g1, &g2);
        panic!();
    }
}
