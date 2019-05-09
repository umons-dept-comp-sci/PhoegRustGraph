use Set;


/// Structure storing the transformation applied to a graph in a compact way.
pub struct GraphTransformation {
    prev_n: u64,
    n: u64,
    prev_m: u64,
    m: u64,
    data: Vec<Set>,
    name: String,
    result: Option<Graph>,
}

impl GraphTransformation {
    /// Constructs a new empty GraphTransformation object with n vertices.
    ///
    /// # Examples :
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// let gt = GraphTransformation::new(0);
    /// assert_eq!(gt.order(),0);
    /// assert_eq!(gt.size(),0);
    /// let gt = GraphTransformation::new(5);
    /// assert_eq!(gt.order(),5);
    /// assert_eq!(gt.size(),0);
    /// for i in 0..5 {
    ///     for j in 0..5 {
    ///         if i == j {
    ///             assert!(gt.is_vertex(i));
    ///             assert!(!gt.is_vertex_modified(i));
    ///         } else {
    ///             assert!(!gt.is_edge(i,j));
    ///             assert!(!gt.is_edge_modified(i,j));
    ///         }
    ///     }
    /// }
    /// ```
    pub fn new(n: u64) -> GraphTransformation {
        let mut v = Vec::with_capacity(n as usize);
        let mut s;
        for i in 0..n {
            s = Set::new(2 * n);
            s.add(2 * i + 1);
            v.push(s);
        }
        GraphTransformation {
            prev_n: n,
            n: n,
            prev_m: 0,
            m: 0,
            data: v,
            name: "".to_owned(),
            result: None,
        }
    }

    pub fn set_name(&mut self, s: String) {
        self.name = s;
    }

    pub fn name(&self) -> String {
        self.name.clone()
    }

    /// Returns the number of vertices of the GraphTransformation before applying the
    /// transformations
    pub fn initial_order(&self) -> u64 {
        self.prev_n
    }

    /// Returns the number of vertices of the GraphTransformation after applying the
    /// transformations
    pub fn order(&self) -> u64 {
        self.n
    }

    /// Returns the number of edges of the GraphTransformation before applying the
    /// transformations
    pub fn initial_size(&self) -> u64 {
        self.prev_m
    }

    /// Returns the number of edges of the GraphTransformation after applying the
    /// transformations
    pub fn size(&self) -> u64 {
        self.m
    }

    /// Returns true if the edge was removed or added from the initial situation.
    pub fn is_edge_modified(&self, i: u64, j: u64) -> bool {
        self.data[i as usize].contains(2 * j)
    }

    /// Returns true if the graph currently has the given edge. To know if the initial graph had
    /// the edge, either it was not modified and the current graph has the edge or it was modified
    /// and the edge is absent (e.g., it was removed).
    pub fn is_edge(&self, i: u64, j: u64) -> bool {
        self.data[i as usize].contains(2 * j + 1)
    }

    /// Returns true if the vertex was removed or added from the initial situation.
    pub fn is_vertex_modified(&self, i: u64) -> bool {
        self.data[i as usize].contains(2 * i)
    }

    /// Returns true if the graph currently has the given vertex. To know if the initial graph had
    /// the vertex, either it was not modified and the current graph has the edge or it was modified
    /// and the vertex is absent (e.g., it was removed).
    pub fn is_vertex(&self, i: u64) -> bool {
        self.data[i as usize].contains(2 * i + 1)
    }

    /// Returns the maximal vertex index of the graph. i.e., if a graph had 0 to 5 vertices and we
    /// remove vertex 3, it now has 5 vertices but its maximal index is still 5 since vertex 5 was
    /// not removed.
    pub fn max_vertex(&self) -> u64 {
        self.data.len().saturating_sub(1) as u64
    }

    /// Adds an edge to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::Graph;
    ///
    /// let mut g = Graph::new(3);
    /// g.add_edge(1,0);
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.add_edge(1,0);
    /// assert!(gt.is_edge(1,0));
    /// assert!(!gt.is_edge_modified(1,0));
    /// assert_eq!(gt.initial_size(),1);
    /// assert_eq!(gt.size(),1);
    /// gt.add_edge(1, 2);
    /// assert_eq!(gt.initial_size(),1);
    /// assert_eq!(gt.size(),2);
    /// assert!(gt.is_edge(1,2));
    /// assert!(gt.is_edge_modified(1,2));
    /// gt.remove_edge(1,0);
    /// gt.add_edge(1,0);
    /// assert_eq!(gt.initial_size(),1);
    /// assert_eq!(gt.size(),2);
    /// assert!(gt.is_edge(1,0));
    /// assert!(!gt.is_edge_modified(1,0));
    /// ```
    pub fn add_edge(&mut self, i: u64, j: u64) {
        if i != j && !self.is_edge(i, j) {
            self.data[i as usize].add(2 * j + 1);
            self.data[i as usize].flip(2 * j);
            self.data[j as usize].add(2 * i + 1);
            self.data[j as usize].flip(2 * i);
            self.m += 1;
            self.result = None;
        }
    }

    /// Adds an edge to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::Graph;
    ///
    /// let mut g = Graph::new(3);
    /// g.add_edge(1,2);
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.remove_edge(1,0);
    /// assert!(!gt.is_edge(1,0));
    /// assert!(!gt.is_edge_modified(1,0));
    /// assert_eq!(gt.size(),1);
    /// assert_eq!(gt.initial_size(),1);
    /// gt.remove_edge(1, 2);
    /// assert_eq!(gt.size(),0);
    /// assert_eq!(gt.initial_size(),1);
    /// assert!(!gt.is_edge(1,2));
    /// assert!(gt.is_edge_modified(1,2));
    /// gt.add_edge(1,0);
    /// gt.remove_edge(1,0);
    /// assert_eq!(gt.size(),0);
    /// assert_eq!(gt.initial_size(),1);
    /// assert!(!gt.is_edge(1,0));
    /// assert!(!gt.is_edge_modified(1,0));
    /// ```
    pub fn remove_edge(&mut self, i: u64, j: u64) {
        if i != j && self.is_edge(i, j) {
            self.data[i as usize].remove(2 * j + 1);
            self.data[i as usize].flip(2 * j);
            self.data[j as usize].remove(2 * i + 1);
            self.data[j as usize].flip(2 * i);
            self.m -= 1;
            self.result = None;
        }
    }

    /// Adds a vertex to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::Graph;
    ///
    /// let mut g = Graph::new(3);
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.add_vertex(2);
    /// assert!(gt.is_vertex(2));
    /// assert!(!gt.is_vertex_modified(2));
    /// gt.add_vertex(3);
    /// assert_eq!(gt.order(),4);
    /// assert_eq!(gt.initial_order(),3);
    /// assert!(gt.is_vertex(3));
    /// assert!(gt.is_vertex_modified(3));
    /// gt.remove_vertex(2);
    /// gt.add_vertex(2);
    /// assert!(gt.is_vertex(2));
    /// assert!(!gt.is_vertex_modified(2));
    /// ```
    pub fn add_vertex(&mut self, i: u64) {
        assert!(i as usize <= self.data.len());
        if i as usize == self.data.len() {
            let max = if self.data.len() > 0 {
                self.data[0].getmax() + 2
            } else {
                0
            };
            for v in self.data.iter_mut() {
                (*v).setmax(max);
            }
            let mut new_set = Set::new(max);
            new_set.add(2 * i);
            new_set.add(2 * i + 1);
            self.data.push(new_set);
            self.n += 1;
        } else if !self.is_vertex(i) {
            self.data[i as usize].add(2 * i + 1);
            self.data[i as usize].flip(2 * i);
            self.n += 1;
        }
        self.result = None;
    }

    /// Removes a vertex to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::Graph;
    ///
    /// let mut g = Graph::new(4);
    /// g.add_edge(2,1);
    /// g.add_edge(2,3);
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.remove_vertex(2);
    /// assert!(!gt.is_vertex(2));
    /// assert!(gt.is_vertex_modified(2));
    /// for &i in [1,3].iter() {
    ///     assert!(!gt.is_edge(2,i));
    ///     assert!(gt.is_edge_modified(2,i));
    /// }
    /// assert_eq!(gt.order(),3);
    /// assert_eq!(gt.initial_order(),4);
    /// gt.remove_vertex(2);
    /// assert_eq!(gt.order(),3);
    /// assert_eq!(gt.initial_order(),4);
    /// assert!(!gt.is_vertex(2));
    /// assert!(gt.is_vertex_modified(2));
    /// gt.add_vertex(4);
    /// gt.remove_vertex(4);
    /// assert!(!gt.is_vertex(4));
    /// assert!(!gt.is_vertex_modified(4));
    /// assert_eq!(gt.order(),3);
    /// assert_eq!(gt.initial_order(),4);
    /// ```
    pub fn remove_vertex(&mut self, i: u64) {
        if self.is_vertex(i) {
            self.data[i as usize].remove(2 * i + 1);
            self.data[i as usize].flip(2 * i);
            for j in (0..self.n).filter(|&x| x != i) {
                self.remove_edge(i, j);
            }
            self.n -= 1;
            self.result = None;
        }
    }

    /// Returns the initial graph used to construct the GraphTransformation.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::Graph;
    /// use graph::transfo_result::GraphTransformation;
    ///
    /// let g = Graph::new(0);
    /// let gt: GraphTransformation = (&g).into();
    /// let g = gt.initial_graph();
    /// assert_eq!(g.order(),0);
    /// assert_eq!(g.size(),0);
    /// assert_eq!(g.edges().count(),0);
    /// let mut g = Graph::new(5);
    /// let edges = [(0,1), (0,2), (3,4)];
    /// for (i,j) in edges.iter() {
    ///     g.add_edge(*i,*j);
    /// }
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.remove_edge(0,1);
    /// gt.add_edge(1,4);
    /// gt.remove_vertex(1);
    /// gt.add_vertex(5);
    /// let res_g = gt.initial_graph();
    /// assert_eq!(res_g.order(),5);
    /// assert_eq!(res_g.size(),3);
    /// for ((i,j),(ri,rj)) in res_g.edges().zip(edges.iter()) {
    ///     assert_eq!(i,*ri);
    ///     assert_eq!(j,*rj);
    /// }
    /// ```
    pub fn initial_graph(&self) -> Graph {
        let mut graph = Graph::new(self.initial_order());
        let w = graph.w;
        let mut res = graph.data;
        let mut gp = 0;
        let mut current;
        let mut current_mask;
        // For each vertex that was in the initial graph (0..prev_n)
        for i in 0..(self.prev_n as usize) {
            // For each word in this vertex's set that was not added afterwards (they can only be
            // i.e., we only take as many words as needed for prev_n vertices
            // at the end of a word)
            for p in (0..w as usize).step_by(2) {
                // extract the modified and the adjacency info
                current = untwine(self.data[i].data[p]) << 32;
                current_mask = untwine(self.data[i].data[p] >> 1) << 32;
                if p < w as usize - 1 {
                    current |= untwine(self.data[i].data[p + 1]);
                    current_mask |= untwine(self.data[i].data[p + 1] >> 1);
                }
                // xor them together to get the initial value
                current ^= current_mask;
                // and add it as one word to the result
                res[gp] = current;
                gp += 1;
            }
        }
        // then create a graph and return the result
        graph.data = res;
        graph.m = self.prev_m;
        graph
    }

    /// Returns the graph obtained by applying the transformations to the initial graph
    ///
    /// # Examples :
    /// ```
    /// use graph::Graph;
    /// use graph::transfo_result::GraphTransformation;
    ///
    /// let g = Graph::new(0);
    /// let mut gt: GraphTransformation = (&g).into();
    /// let g = gt.final_graph();
    /// assert_eq!(g.order(),0);
    /// assert_eq!(g.size(),0);
    /// assert_eq!(g.edges().count(),0);
    /// let mut g = Graph::new(5);
    /// let mut edges = vec![(0,1), (0,2), (3,4)];
    /// for (i,j) in edges.iter() {
    ///     g.add_edge(*i,*j);
    /// }
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.remove_edge(0,1);
    /// gt.add_edge(1,4);
    /// gt.remove_vertex(1);
    /// gt.add_vertex(5);
    /// gt.add_vertex(6);
    /// gt.add_edge(2,6);
    /// edges = vec![(0,1), (1,5), (2,3)];
    /// let res_g = gt.final_graph();
    /// assert_eq!(res_g.order(),6,"graph must have right order");
    /// assert_eq!(res_g.size(),3, "graph must have right size");
    /// for ((i,j),(ri,rj)) in res_g.edges().zip(edges.iter()) {
    ///     assert_eq!(i,*ri, "edge must have fist vertex {}",i);
    ///     assert_eq!(j,*rj, "edge must have last vertex {}",j);
    /// }
    /// ```
    pub fn final_graph(&mut self) -> Graph {
        if self.result.is_none()
        {
            let mut graph = Graph::new(self.order());
            if self.n > 0 {
                let vertices = (0..(self.max_vertex()+1))
                    .filter(|&x| self.is_vertex(x as u64))
                    .collect::<Vec<_>>();
                // For each vertex that was not removed or was added
                for i in (0..vertices.len()).take(self.n as usize - 1) {
                    // We have to iterate over each vertex as we do not know which ones remains.
                    for j in (i + 1)..vertices.len() {
                        if self.is_edge(vertices[i], vertices[j]) {
                            graph.add_edge(i as u64, j as u64);
                        }
                    }
                }
            }
            self.result = Some(graph);
        }
        self.result.clone().unwrap()
    }
}

const DECS: [u64; 6] = [16, 8, 4, 2, 1, 0];
const MASKS: [u64; 6] = [0x00000000FFFFFFFF,
                         0x0000FFFF0000FFFF,
                         0x00FF00FF00FF00FF,
                         0x0F0F0F0F0F0F0F0F,
                         0x3333333333333333,
                         0x5555555555555555];

fn untwine(v: u64) -> u64 {
    let mut p = v;
    for i in (0..DECS.len()).map(|x| DECS.len() - x - 1) {
        p = (p | (p >> DECS[i])) & MASKS[i];
    }
    p
}

fn interleave(v: u32) -> u64 {
    let mut p: u64 = v as u64;
    for i in 0..DECS.len() - 1 {
        p = (p | (p << DECS[i])) & MASKS[i + 1];
    }
    p
}

lazy_static! {
    static ref counters: [u8; 256] = {
        let mut c = [0; 256];
        for i in 0..256 {
            c[i as usize] = (i & 1) as u8 + c[(i/2) as usize];
        }
        c
    };
}

fn num_bits(v: u32) -> u64 {
    let v = v as usize;
    counters[v & 0xff] as u64 + counters[v >> 8 & 0xff] as u64 + counters[v >> 16 & 0xff] as u64 +
    counters[v >> 24 & 0xff] as u64
}

use Graph;
use std::convert::From;
impl From<&Graph> for GraphTransformation {
    fn from(graph: &Graph) -> Self {
        // Get number of words per vertex
        let w = graph.w;
        // Get binary representation
        let repr = graph.data.clone();
        let n = graph.n;
        let m = graph.m;
        let mut res = Vec::with_capacity(n as usize);
        let mut cur = Vec::with_capacity(w as usize);
        let mut tmp;
        let mut st;
        let mut size;
        // for each vertex
        for v in (0..n as usize).map(|x| x * w as usize) {
            cur.clear();
            size = 0;
            // for each word of this vertex line
            for p in (0..w as usize).map(|x| x + v) {
                // expand the word into two words
                tmp = (repr[p] >> 32) as u32;
                size += num_bits(tmp);
                cur.push(interleave(tmp));
                tmp = (repr[p] & ((1 << 32) - 1)) as u32;
                size += num_bits(tmp);
                cur.push(interleave(tmp));
            }
            // create a set from the obtained words
            // add it to the vector
            st = Set {
                maxm: 2 * n,
                size: size,
                data: cur.clone(),
            };
            st.add((2 * v + 1) as u64);
            res.push(st);
        }
        GraphTransformation {
            prev_n: n,
            n: n,
            prev_m: m,
            m: m,
            data: res,
            result: None,
            name: "".to_owned(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from() {
        let mut g = Graph::new(5);
        g.add_cycle(&(0..5).collect::<Vec<_>>());
        let gt = GraphTransformation::from(&g);
        for i in 0u64..5 {
            for j in 0u64..5 {
                dbg!((i, j));
                if (i as i64 - j as i64).abs() == 1 || (i as i64 - j as i64).abs() == 4 || i == j {
                    assert!(gt.is_edge(i, j));
                } else {
                    assert!(!gt.is_edge(i, j));
                }
                assert!(!gt.is_edge_modified(i, j));
            }
        }
    }

    #[test]
    fn test_interleave_untwine() {
        let v1 = 0b11011001;
        let v2 = 0b00111011;
        let v = interleave(v1 as u32) | (interleave(v2 as u32) << 1);
        assert_eq!(0b0101101111001011, v);
        let res_v1 = untwine(v);
        assert_eq!(v1, res_v1);
        let res_v2 = untwine(v >> 1);
        assert_eq!(v2, res_v2);
    }
}
