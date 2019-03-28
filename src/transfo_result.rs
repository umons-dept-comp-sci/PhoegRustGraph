use Set;


pub struct GraphTransformation {
    prev_n: u64,
    n: u64,
    prev_m: u64,
    m: u64,
    data: Vec<Set>,
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
        }
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
        }
    }
}

const DECS: [u64; 5] = [16, 8, 4, 2, 1];
const MASKS: [u64; 5] = [0x0000FFFF0000FFFF,
                         0x00FF00FF00FF00FF,
                         0x0F0F0F0F0F0F0F0F,
                         0x3333333333333333,
                         0x5555555555555555];

fn interleave(v: u32) -> u64 {
    let mut p: u64 = v as u64;
    for i in 0..DECS.len() {
        p = (p | (p << DECS[i])) & MASKS[i];
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
    counters[v & 0xff] as u64 + counters[v.wrapping_shr(8) & 0xff] as u64 +
    counters[v.wrapping_shr(16) & 0xff] as u64 + counters[v.wrapping_shr(24) & 0xff] as u64
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
                tmp = repr[p].wrapping_shr(32) as u32;
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
}
