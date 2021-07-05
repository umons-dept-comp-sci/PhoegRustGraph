use crate::nauty::canon_graph;
use crate::Set;
use base64;

fn format_arr_csv<T: std::fmt::Debug>(arr: &[T]) -> String {
    arr.iter()
        .map(|x| format!("{:?}", x))
        .collect::<Vec<String>>()
        .join(";")
}

/// Structure storing the transformation applied to a graph in a compact way.
#[repr(C)]
#[derive(Clone)]
pub struct GraphTransformation {
    prev_n: u64,
    n: u64,
    prev_m: u64,
    m: u64,
    data: Vec<Set>,
    name: String,
    result: Option<GraphNauty>,
    order: Option<Vec<u64>>,
    changed: i64,
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
            order: None,
            changed: 0,
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

    /// Returns true if the graph was changed and false otherwise. i.e., if an edge was removed,
    /// the graph is changed. If the edge that should have been removed does not exist or if it was
    /// added later, the graph is unchanged.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::{Graph,GraphNauty};
    ///
    /// let mut g = GraphNauty::new(3);
    /// g.add_edge(1, 0);
    /// let mut gt: GraphTransformation = (&g).into();
    /// assert!(!gt.is_changed());
    /// gt.remove_edge(1, 0);
    /// assert!(gt.is_changed());
    /// gt.add_edge(1, 0);
    /// assert!(!gt.is_changed());
    /// gt.remove_vertex(0);
    /// assert!(gt.is_changed());
    /// gt.add_vertex(0);
    /// assert!(gt.is_changed());
    /// gt.add_edge(1, 0);
    /// assert!(!gt.is_changed());
    /// ```
    pub fn is_changed(&self) -> bool {
        self.changed != 0
    }

    /// Adds an edge to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::{Graph,GraphNauty};
    ///
    /// let mut g = GraphNauty::new(3);
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
        if i != j && self.is_vertex(i) && self.is_vertex(j) && !self.is_edge(i, j) {
            self.data[i as usize].add(2 * j + 1);
            self.data[i as usize].flip(2 * j);
            self.data[j as usize].add(2 * i + 1);
            self.data[j as usize].flip(2 * i);
            self.m += 1;
            self.result = None;
            self.order = None;
            self.changed += self.data[i as usize].contains(2 * j) as i64 * 2 - 1;
            self.changed += self.data[j as usize].contains(2 * i) as i64 * 2 - 1;
        }
    }

    /// Adds an edge to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::{Graph,GraphNauty};
    ///
    /// let mut g = GraphNauty::new(3);
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
            self.order = None;
            self.changed += self.data[i as usize].contains(2 * j) as i64 * 2 - 1;
            self.changed += self.data[j as usize].contains(2 * i) as i64 * 2 - 1;
        }
    }

    /// Adds a vertex to the current graph. The GraphTransformation keeps the same labels for
    /// vertices as in the initial graph (except for added vertices whose labels starts at n, the
    /// number of vertices in the initial graph). Thus, this new order can be applied to vertices
    /// of the initial graph by simply ignoring the vertices added by the transformation.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::{Graph,GraphNauty};
    ///
    /// let mut g = GraphNauty::new(0);
    /// let mut gt: GraphTransformation = (&g).into();
    /// gt.add_vertex(0);
    /// assert_eq!(gt.order(), 1);
    /// g = GraphNauty::new(3);
    /// gt = (&g).into();
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
            let max = if !self.data.is_empty() {
                self.data[0].getmax() + 2
            } else {
                2
            };
            for v in self.data.iter_mut() {
                (*v).setmax(max);
            }
            let mut new_set = Set::new(max);
            new_set.add(2 * i);
            new_set.add(2 * i + 1);
            self.data.push(new_set);
            self.n += 1;
            self.changed += self.data[i as usize].contains(2 * i) as i64 * 2 - 1;
        } else if !self.is_vertex(i) {
            self.data[i as usize].add(2 * i + 1);
            self.data[i as usize].flip(2 * i);
            self.n += 1;
            self.changed += self.data[i as usize].contains(2 * i) as i64 * 2 - 1;
        }
        self.result = None;
        self.order = None;
    }

    /// Removes a vertex to the current graph.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::transfo_result::GraphTransformation;
    /// use graph::{Graph,GraphNauty};
    ///
    /// let mut g = GraphNauty::new(4);
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
            self.order = None;
            self.changed += self.data[i as usize].contains(2 * i) as i64 * 2 - 1;
        }
    }

    /// Returns the initial graph used to construct the GraphTransformation.
    ///
    /// # Examples :
    ///
    /// ```
    /// use graph::{Graph,GraphNauty,GraphIter};
    /// use graph::transfo_result::GraphTransformation;
    ///
    /// let g = GraphNauty::new(0);
    /// let gt: GraphTransformation = (&g).into();
    /// let g = gt.initial_graph();
    /// assert_eq!(g.order(),0);
    /// assert_eq!(g.size(),0);
    /// let mut m = 0;
    /// let mut vi = g.vertices();
    /// while let Some(v) = vi.next() {
    ///     let mut wi = vi.clone();
    ///     for w in wi.filter(|x| g.is_edge(v,*x)) {
    ///         m += 1;
    ///     }
    /// }
    /// assert_eq!(m,0);
    /// let mut g = GraphNauty::new(5);
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
    /// let mut vi = res_g.vertices();
    /// let mut i = 0;
    /// while let Some(v) = vi.next() {
    ///     let mut wi = vi.clone();
    ///     for w in wi.filter(|x| res_g.is_edge(v,*x)) {
    ///         let (ri,rj) = edges[i];
    ///         assert_eq!(v,ri);
    ///         assert_eq!(w,rj);
    ///         i += 1;
    ///     }
    /// }
    /// ```
    pub fn initial_graph(&self) -> GraphNauty {
        let mut graph = GraphNauty::new(self.initial_order());
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
        for i in 0..self.prev_n {
            graph.remove_edge(i, i);
        }
        graph
    }

    fn compute_final_graph(&self) -> GraphNauty {
        let mut graph = GraphNauty::new(self.order());
        if self.n > 0 {
            let vertices = (0..=self.max_vertex())
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
        graph
    }

    /// Returns the graph obtained by applying the transformations to the initial graph
    ///
    /// # Examples :
    /// ```
    /// use graph::{Graph,GraphNauty,GraphIter};
    /// use graph::transfo_result::GraphTransformation;
    ///
    /// let g = GraphNauty::new(0);
    /// let mut gt: GraphTransformation = (&g).into();
    /// let g = gt.final_graph();
    /// assert_eq!(g.order(),0);
    /// assert_eq!(g.size(),0);
    /// let m = g.vertices().flat_map(|x| g.neighbors(x).zip(std::iter::repeat(x))).count();
    /// assert_eq!(m,0);
    /// let mut g = GraphNauty::new(5);
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
    /// let mut edges_iter = edges.iter();
    /// let mut verts = res_g.vertices();
    /// while let Some(i) = verts.next() {
    ///     let mut verts2 = verts.clone();
    ///     while let Some(j) = verts2.next() {
    ///         if res_g.is_edge(i,j) {
    ///             let e = edges_iter.next();
    ///             assert!(e.is_some());
    ///             let (ri,rj) = e.unwrap();
    ///             assert_eq!(i,*ri, "edge must have fist vertex {}",i);
    ///             assert_eq!(j,*rj, "edge must have last vertex {}",j);
    ///         }
    ///     }
    /// }
    /// ```
    pub fn final_graph(&mut self) -> GraphNauty {
        if self.result.is_none() {
            let graph = self.compute_final_graph();
            self.result = Some(graph);
            self.order = None;
        }
        self.result.clone().unwrap()
    }

    /// Computes the canonical form of the result as well as the order of the vertices in this
    /// form.
    pub fn canon(&mut self) {
        let (cg, ord, _) = canon_graph(&self.final_graph());
        self.result = Some(cg);
        self.order = Some(ord);
    }

    /// Computes the canonical form of the result as well as the order of the vertices in this form
    /// (if not already computed). And returns the canonical ordering of the vertices.
    pub fn canon_order(&mut self) -> Vec<u64> {
        if self.order.is_none() {
            self.canon();
        }
        self.order.clone().unwrap()
    }

    pub fn tocsv(&self) -> String {
        format!(
            "{}, {}, {:?}, {}, {}",
            self.name,
            self.initial_graph(),
            self.result.clone().unwrap(),
            self,
            format_arr_csv(&self.order.clone().unwrap())
        )
    }

    pub fn to_incorrect(&self) -> String {
        let mut added_v = Vec::new();
        let mut added_e = Vec::new();
        let mut removed_v = Vec::new();
        let mut removed_e = Vec::new();
        for u in 0..=self.max_vertex() {
            if self.is_vertex_modified(u) {
                if self.is_vertex(u) {
                    added_v.push(u);
                } else {
                    removed_v.push(u);
                }
            }
            if self.is_vertex(u) && u < self.max_vertex() {
                for v in u+1..=self.max_vertex() {
                    if v != u && self.is_vertex(v) {
                        if self.is_edge_modified(u, v) {
                            if self.is_edge(u, v) {
                                added_e.push(format!("({}, {})", u, v));
                            } else {
                                removed_e.push(format!("({}, {})", u, v));
                            }
                        }
                    }
                }
            }
        }
        let mut res = format!(
            "{}, {}, {:?}, {}",
            self.name,
            self.initial_graph(),
            self.result.clone().unwrap(),
            self,
        );
        for (txt, arr) in &[(",added vertices:", added_v), (",removed_vertices:", removed_v)] {
            if !arr.is_empty() {
                res.push_str(txt);
                res.push_str(&format_arr_csv(&arr));
            }
        }
        for (txt, arr) in &[(",added_edges:", added_e), (",removed_edges:", removed_e)] {
            if !arr.is_empty() {
                res.push_str(txt);
                res.push_str(&format_arr_csv(&arr));
            }
        }
        res
    }

    /// Reorder the vertices of a GraphTransformation by using the new order given as parameter.
    /// Note that the initial graph is no longer the same since its vertices are reordered.
    // TODO: Error
    pub fn reorder(&self, order: &[u64]) -> Result<GraphTransformation, ()> {
        if order.len() as u64 == self.max_vertex() + 1 {
            let mut res = self.clone();
            let n = self.max_vertex() + 1;
            for i in 0..n {
                if i < order.len() as u64 && order[i as usize] < n {
                    for j in 0..n {
                        if j < order.len() as u64 && order[j as usize] < n {
                            for k in 0..=1 {
                                if self.data[i as usize].contains(2 * j + k) {
                                    res.data[order[i as usize] as usize]
                                        .add(2 * order[j as usize] + k);
                                } else {
                                    res.data[order[i as usize] as usize]
                                        .remove(2 * order[j as usize] + k);
                                }
                            }
                        } else {
                            return Err(());
                        }
                    }
                } else {
                    return Err(());
                }
            }
            res.order = None;
            res.result = None;
            Ok(res)
        } else {
            Err(())
        }
    }
}

use crate::format::Converter;
use std::fmt;
impl fmt::Display for GraphTransformation {
    /// This function converts a GraphTransformation into a string using a format defined to be as
    /// compact as possible.
    /// It uses a binary representation before converting it using base64.
    /// First, the order of the GraphTransformation is encoded. It is split into at most 9 groups
    /// of 7 bits from less significant to most. We transform each group to groups of 8 bits by
    /// adding 127 to each group but the last. If the remaining bit is 1 (n > 2^63), we add 127 to
    /// the last group as well. Otherwise, it retain the same value but is now encoded on 8 bits.
    /// These groups form the encoding of the order.
    ///
    /// Example:
    /// Let n be the order.
    /// If n = 5 = 101, the order will be encoded as 00000101
    /// If n = 354 = 101100010, we split this in groups of 7 bits from right to left:
    /// 1100010 0000010
    /// We add 127 (or 10000000) to each group but the last:
    /// 11100010 00000010
    ///
    /// Once the order of the transformation has been encoded, the rest is encoded using the lower
    /// triangle part of the adjacency matrix plus the diagonal. There are 2 bits per vertex/edge.
    /// The first bit (left) indicates whether the element is present and the second one tells if
    /// it was changed by the transformation (added or removed).
    ///
    /// Example:
    /// Let g be a graph with 3 vertices such that 0 and 1 are adjacent.
    /// Let t be the transformation adding edge 1 2 and removing vertex 0.
    /// t would be represented as follows :
    /// 10 10 00  0 and its edges are removed but vertex 0 and edge 01 changed
    /// 10 01 11  1 is now adjacent to 2 and no longer to 0
    /// 00 11 01  2 is now adjacent to 1
    ///
    /// The lower triangle + diagonal is as follows :
    /// 10 10 01 00 11 01
    ///
    /// Putting everything together (order and matrix), we get the following (as bytes):
    /// 00000011 10100100 11010000
    /// In base64 : A6TQ
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let n = self.max_vertex() as usize + 1;
        if n == 0 {
            write!(f, "{}", base64::encode(&[0]))
        } else {
            let num_bits = n * (n - 1) + 2 * n;
            let num_words = (num_bits - 1) / 64 + 1;
            let mut c = Converter::new(&vec![64; num_words]);
            for i in 0..n {
                c.feed(2 * (i + 1) as u64, &self.data[i].data);
            }
            let mut r = c.result();
            let mut res = String::new();
            unsafe {
                let t = r.align_to_mut::<u8>().1;
                for i in 0..num_words {
                    t[i * 8..(i + 1) * 8].reverse();
                }
                let mut encode = encode_num(n as u64);
                encode.extend_from_slice(&t[0..=num_bits / 8]);
                base64::encode_config_buf(&encode, base64::STANDARD, &mut res);
            }
            //TODO add an option to output it or not
            //if !self.name.is_empty() {
            //write!(f, "{}:", self.name)?;
            //}
            write!(f, "{}", res)
        }
    }
}

impl fmt::Debug for GraphTransformation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} : {} -> {:?} [changes: {}, order: {:?}]",
            self.name,
            self.initial_graph(),
            self.result,
            self,
            self.order
        )
    }
}

use std::convert::TryFrom;

impl TryFrom<&str> for GraphTransformation {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, ()> {
        // TODO define error
        let v: Vec<&str> = value.split(':').collect();
        let mut name = "";
        let value = if v.len() > 1 {
            name = v[0];
            v[1]
        } else {
            value
        };
        let bytes = base64::decode(value).unwrap(); //TODO error
        let (n, p) = decode_num(&bytes);
        let mut r: [u8; 8] = [0; 8];
        let nbytes = n * (n - 1) + 2 * n;
        let mut scheme = Vec::with_capacity(n as usize);
        for i in 0..n {
            scheme.push(2 * (i + 1));
        }
        let mut c = Converter::new(&scheme);
        for i in (p..bytes.len()).step_by(8) {
            let lim = std::cmp::min(8, bytes.len() - i);
            r[..lim].clone_from_slice(&bytes[i..lim + i]);
            //for j in 0..(std::cmp::min(8, bytes.len() - i)) {
            //r[j] = bytes[i + j];
            //}
            c.feed(
                std::cmp::min(64, nbytes - (i - p) as u64 * 8),
                &[u64::from_be_bytes(r)],
            );
        }
        let r = c.result();
        let mut result = GraphTransformation::new(n);
        let mut p = 0;
        for i in 0..n {
            for j in 0..=(2 * (i + 1) - 1) / 64 {
                result.data[i as usize].data[j as usize] = r[p];
                p += 1;
            }
        }
        // Recompute the symmetrical part that was removed
        for i in 1..n {
            for j in 0..i {
                for k in 0..2 {
                    if result.data[i as usize].contains(2 * j + k) {
                        result.data[j as usize].add(2 * i + k);
                    }
                }
            }
        }
        // Recompute the other data (initial_order, initial_size, order, size, ...)
        let (mut pn, mut nn, mut pm, mut nm) = (0, 0, 0, 0);
        for i in 0..n {
            if result.is_vertex(i) {
                nn += 1;
            }
            if result.is_vertex_modified(i) ^ result.is_vertex(i) {
                pn += 1;
            }
        }
        for i in 1..n {
            for j in 0..i {
                if result.is_edge(i, j) {
                    nm += 1;
                }
                if result.is_edge_modified(i, j) ^ result.is_edge(i, j) {
                    pm += 1;
                }
            }
        }
        result.prev_n = pn;
        result.n = nn;
        result.prev_m = pm;
        result.m = nm;
        result.set_name(name.to_owned());
        Ok(result)
    }
}

fn encode_num(n: u64) -> Vec<u8> {
    let mut r = Vec::with_capacity(9);
    let mut n = n;
    let mut v: u8;
    while n > 0 && r.len() < 9 {
        v = (n & 127) as u8;
        n = n.wrapping_shr(7);
        if n > 0 {
            v += 128;
        }
        r.push(v);
    }
    r
}

fn decode_num(data: &[u8]) -> (u64, usize) {
    if data.is_empty() {
        return (0, 0);
    }
    let mut res = 0;
    let mut p = 0;
    let mut cont = true;
    let mut val;
    while cont && p < 9 {
        val = data[p] & 127;
        cont = data[p] > 127;
        res |= u64::from(val) << (p * 7);
        p += 1;
    }
    if cont {
        res |= 1 << 63;
    }
    (res, p)
}

const DECS: [u64; 6] = [16, 8, 4, 2, 1, 0];
const MASKS: [u64; 6] = [
    0x0000_0000_FFFF_FFFF,
    0x0000_FFFF_0000_FFFF,
    0x00FF_00FF_00FF_00FF,
    0x0F0F_0F0F_0F0F_0F0F,
    0x3333_3333_3333_3333,
    0x5555_5555_5555_5555,
];

fn untwine(v: u64) -> u64 {
    let mut p = v;
    for i in (0..DECS.len()).map(|x| DECS.len() - x - 1) {
        p = (p | (p >> DECS[i])) & MASKS[i];
    }
    p
}

fn interleave(v: u32) -> u64 {
    let mut p: u64 = u64::from(v);
    for i in 0..DECS.len() - 1 {
        p = (p | (p << DECS[i])) & MASKS[i + 1];
    }
    p
}

lazy_static! {
    static ref COUNTERS: [u8; 256] = {
        let mut c = [0; 256];
        for i in 0..256 {
            c[i as usize] = (i & 1) as u8 + c[(i / 2) as usize];
        }
        c
    };
}

fn num_bits(v: u32) -> u64 {
    let v = v as usize;
    u64::from(COUNTERS[v & 0xff])
        + u64::from(COUNTERS[v >> 8 & 0xff])
        + u64::from(COUNTERS[v >> 16 & 0xff])
        + u64::from(COUNTERS[v >> 24 & 0xff])
}

use crate::Graph;
use crate::GraphNauty;
use std::convert::From;
impl From<&GraphNauty> for GraphTransformation {
    fn from(graph: &GraphNauty) -> Self {
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
                if n > 32 {
                    tmp = (repr[p] & ((1 << 32) - 1)) as u32;
                    size += num_bits(tmp);
                    cur.push(interleave(tmp));
                }
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
            order: None,
            name: "".to_owned(),
            changed: 0,
        }
    }
}

use std::convert::Into;
impl Into<GraphNauty> for GraphTransformation {
    fn into(self) -> GraphNauty {
        self.compute_final_graph()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::from_g6;
    use std::convert::TryInto;

    #[test]
    fn test_from() {
        let mut g = GraphNauty::new(5);
        g.add_cycle(&(0..5).collect::<Vec<_>>());
        let gt = GraphTransformation::from(&g);
        for i in 0u64..5 {
            for j in 0u64..5 {
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

    #[test]
    fn test_encode_num() {
        let mut res = encode_num(7);
        assert_eq!(&res, &[7]);
        res = encode_num(0xffaa);
        assert_eq!(&res, &[0xaa, 0xff, 0x3]);
        res = encode_num(0xffffffffffffffff);
        assert_eq!(
            &res,
            &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
        );
    }

    #[test]
    fn test_decode_num() {
        let (res, p) = decode_num(&[7]);
        assert_eq!(7, res);
        assert_eq!(1, p);
        let (res, p) = decode_num(&[0xaa, 0xff, 0x3]);
        assert_eq!(res, 0xffaa);
        assert_eq!(3, p);
        let (res, p) = decode_num(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(res, 0xffffffffffffffff);
        assert_eq!(9, p);
    }

    #[test]
    fn test_fmt_graphtransformation() {
        let g: GraphNauty = from_g6("DB{").unwrap();
        let exp_res: GraphNauty = from_g6("EAf?").unwrap();
        let mut gt: GraphTransformation = (&g).into();
        gt.remove_vertex(2);
        gt.add_vertex(5);
        gt.remove_edge(1, 4);
        gt.add_edge(1, 5);
        gt.add_edge(0, 5);
        let r = format!("{}", gt);
        gt = (r.as_str()).try_into().unwrap();
        assert_eq!(gt.order(), 5);
        assert_eq!(gt.size(), exp_res.size());
        assert!(!gt.is_vertex(2));
        assert!(gt.is_vertex_modified(2));
        for i in (0..6 as u64).filter(|x| *x != 2) {
            assert!(gt.is_vertex(i));
            if i < 5 {
                assert!(!gt.is_vertex_modified(i));
            } else {
                assert!(gt.is_vertex_modified(i));
            }
            for j in (0..6 as u64).filter(|x| *x != 2 && *x != i) {
                assert_eq!(gt.is_edge(i, j), exp_res.is_edge(i, j));
                assert_eq!(
                    exp_res.is_edge(i, j) != g.is_edge(i, j),
                    gt.is_edge_modified(i, j)
                );
            }
        }
    }
}
