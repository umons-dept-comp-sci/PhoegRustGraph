//! Crate using binary format to represent small graphs (order <= 11)

//#![feature(trace_macros)]

extern crate bit_vec;
extern crate libc;

pub mod format;
pub mod invariants;
pub mod errors;
pub mod nauty;
#[macro_use]
mod transfos_macros;
pub mod transfos;
pub mod subgraphs;

use std::fmt;


#[allow(non_camel_case_types)]
#[cfg(target_pointer_width="32")]
type set = libc::c_ulong;
#[allow(non_camel_case_types)]
#[cfg(target_pointer_width="64")]
type set = libc::c_ulonglong;

#[allow(non_camel_case_types)]
// Type used by nauty in C
type int = libc::c_int;
#[allow(non_camel_case_types)]
type graph = set;


mod detail {
    use super::set;
    use super::int;
    use super::graph;
    extern "C" {
        pub fn setwordsneeded(n: int) -> int;
        pub fn emptyset(input: *mut set, size: int);
        pub fn addelement(input: *mut set, elem: int);
        pub fn delelement(input: *mut set, elem: int);
        pub fn flipelement(input: *mut set, elem: int);
        pub fn iselement(input: *const set, elem: int) -> bool;
        #[allow(dead_code)]
        pub fn setsize(input: *const set, size: int) -> int;
        pub fn nextelement(input: *const set, size: int, pos: int) -> int;
        pub fn wordsize() -> int;
        pub fn allbits() -> set;
        pub fn allmask(i: int) -> set;
        #[allow(dead_code)]
        pub fn emptygraph(graph: *mut graph, m: int, n: int);
        pub fn graphrow(graph: *const graph, v: int, m: int) -> *const set;
        pub fn graphrowmut(graph: *mut graph, v: int, m: int) -> *mut set;
        pub fn addoneedge(graph: *mut graph, v: int, w: int, m: int);
    }
}


#[derive(Clone,Debug)]
pub struct Set {
    data: Vec<set>,
    maxm: int,
    size: int,
}

impl Set {
    fn fill<PF>(maxm: int, pfunc: PF, val: set, size: int) -> Set
        where PF: Fn(int) -> set
    {
        unsafe {
            let mut p = maxm;
            let words = detail::setwordsneeded(maxm);
            let mut v = Vec::with_capacity(words as usize);
            for _ in 0..words - 1 {
                v.push(val);
                p -= detail::wordsize();
            }
            v.push(pfunc(p));
            Set {
                data: v,
                maxm: maxm,
                size: size,
            }
        }
    }

    pub fn new(maxm: int) -> Set {
        Set::fill(maxm, |_| 0, 0, 0)
    }

    pub fn full(maxm: int) -> Set {
        unsafe { Set::fill(maxm, |x| detail::allmask(x), detail::allbits(), maxm) }
    }

    pub fn clear(&mut self) {
        unsafe {
            self.size = 0;
            detail::emptyset(self.data.as_mut_ptr(), self.data.len() as int)
        }
    }

    pub fn add(&mut self, elem: int) {
        if !self.contains(elem) {
            self.size += 1;
            unsafe { detail::addelement(self.data.as_mut_ptr(), elem) }
        }
    }

    pub fn remove(&mut self, elem: int) {
        if self.contains(elem) {
            self.size -= 1;
            unsafe { detail::delelement(self.data.as_mut_ptr(), elem) }
        }
    }

    pub fn flip(&mut self, elem: int) {
        unsafe {
            if self.contains(elem) {
                self.size -= 1;
            } else {
                self.size += 1;
            }
            detail::flipelement(self.data.as_mut_ptr(), elem)
        }
    }

    pub fn contains(&self, elem: int) -> bool {
        unsafe { detail::iselement(self.data.as_ptr(), elem) }
    }

    pub fn size(&self) -> i32 {
        self.size
    }

    pub fn iter(&self) -> impl Iterator<Item = int> + '_ {
        SetIter::new(self.data.as_ptr(), self.data.len() as int)
    }

    pub fn maxm(&self) -> int {
        self.maxm
    }

    fn combine<C>(first: &mut Set, other: &Set, comb: C)
        where C: Fn(&set, &set) -> set
    {
        for (i, a) in first.data.iter_mut().enumerate().take_while(|(i, _)| other.data.len() > *i) {
            *a = comb(a, &other.data[i]);
        }
    }

    pub fn inter(&mut self, other: &Set) {
        Set::combine(self, other, |a, b| a & b);
        if self.data.len() > other.data.len() {
            for i in (self.data.len() - other.data.len())..self.data.len() {
                self.data[i] = 0;
            }
        }
    }

    pub fn union(&mut self, other: &Set) {
        if self.data.len() < other.data.len() {
            for _ in (other.data.len() - self.data.len())..other.data.len() {
                self.data.push(0);
            }
        }
        Set::combine(self, other, |&a, &b| a | b)
    }

    fn complement_set(s: *mut set, len: int, maxm: int) {
        let mut s = s;
        let mut maxm = maxm;
        unsafe {
            for _ in 0..(len - 1) {
                *s = !*s;
                maxm -= detail::wordsize();
                s = s.add(1);
            }
            *s = !*s & detail::allmask(maxm);
        }
    }

    pub fn complement(&mut self) {
        Set::complement_set(self.data.as_mut_ptr(), self.data.len() as int, self.maxm);
    }
}

struct SetIter {
    data: *const set,
    len: int,
    pos: int,
}

impl SetIter {
    fn new(data: *const set, len: int) -> SetIter {
        SetIter::with_pos(data, len, -1)
    }

    fn with_pos(data: *const set, len: int, pos: int) -> SetIter {
        SetIter {
            data: data,
            len: len,
            pos: pos,
        }
    }
}

impl Iterator for SetIter {
    type Item = int;

    fn next(&mut self) -> Option<int> {
        unsafe {
            self.pos = detail::nextelement(self.data, self.len, self.pos);
            if self.pos < 0 { None } else { Some(self.pos) }
        }
    }
}

/// Structure representing a undirected simple graph as a binary number.
///
/// The format is the following :
///
///  * The first 4 bits encode the size.
///  * The remaining bits encode the lower triangle of the adjacency matrix and the diagonal.
///    The encoding is made from right to left to allow adding new vertices in constant time.
///
/// For the graph C5 :
/// <pre>
///    0 1 0 1      0
///    1 0 1 0   -> 1 0       -> 1010 | 010 | 01 | 0 | 0101
///    0 1 0 1      0 1 0
///    1 0 1 0      1 0 1 0
/// </pre>
#[derive(Clone)]
pub struct Graph {
    num_vertices: usize,
    num_edges: usize,
    graph: bit_vec::BitVec,
}

/// Returns the position of the bit corresponding to the cell (i,j) of the adjacency matrix.
fn get_position(i: usize, j: usize) -> usize {
    assert!(i != j);
    let mut i = i;
    let mut j = j;
    if i < j {
        std::mem::swap(&mut i, &mut j);
    }
    (i * (i - 1)) / 2 + j
}

impl Graph {
    /// Constructs a new graph with 0 edges and n vertices.
    pub fn new(n: usize) -> Graph {
        Graph {
            num_vertices: n as usize,
            num_edges: 0,
            graph: bit_vec::BitVec::from_elem(n * (std::cmp::max(n, 1) - 1) / 2, false),
        }
    }

    /// Returns the order of the graph
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for _ in 0..11
    /// {
    ///     g.add_vertex();
    /// }
    /// assert!(g.order() == 11);
    /// ```
    pub fn order(&self) -> usize {
        self.num_vertices
    }

    /// Returns the size of the graph
    ///
    /// #Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// assert!(g.size() == 0);
    /// for i in 1..11
    /// {
    ///     for j in 0..i
    ///     {
    ///         g.add_edge(i,j);
    ///     }
    /// }
    /// assert!(g.size() == 11*10/2);
    /// ```
    pub fn size(&self) -> usize {
        self.num_edges
    }

    /// Adds a new vertex to the graph, increasing its order by one.
    /// Will return false if the graph had already an order of 11.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for i in 0..11
    /// {
    ///     g.add_vertex();
    ///     assert!(g.order() == i+1);
    /// }
    /// ```
    pub fn add_vertex(&mut self) {
        self.num_vertices += 1;
        self.graph.grow(self.num_vertices, false);
    }

    // [TODO]: Add unit tests for this.
    /// Removes the vertex i from the graph. The order if the vertices is not conserved.
    /// The last vertex takes the place of the removed one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(7);
    /// for i in g.vertices().skip(1) {
    ///     g.add_edge(i-1,i);
    /// }
    /// g.remove_vertex(7);
    /// assert_eq!(g.order(),7);
    /// g.remove_vertex(6);
    /// assert_eq!(g.order(),6);
    /// g.remove_vertex(0);
    /// assert_eq!(g.order(),5);
    /// g.remove_vertex(3);
    /// assert_eq!(g.order(),4);
    /// ```
    pub fn remove_vertex(&mut self, i: usize) {
        if i < self.order() {
            let last = self.order() - 1;
            if last != i {
                for n in self.vertices() {
                    if n != i && n != last {
                        if self.is_edge(last, n) {
                            self.add_edge(i, n);
                        } else {
                            self.remove_edge(i, n)
                        }
                    }
                }
            }
            self.num_vertices -= 1;
            let n = self.num_vertices;
            self.graph.truncate(n * (std::cmp::max(n, 1) - 1) / 2);
        }
    }

    /// Checks weither the vertices i and j are adjacent.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    /// }
    /// assert!(!g.is_edge(10,0));
    /// ```
    pub fn is_edge(&self, i: usize, j: usize) -> bool {
        let n = self.order();
        i < n && j < n && i != j && (self.graph.get(get_position(i, j)).unwrap())
    }


    /// Adds an edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    ///     assert!(g.size() == i+1);
    /// }
    /// ```
    pub fn add_edge(&mut self, i: usize, j: usize) {
        let n = self.order();
        if i < n && j < n && !self.is_edge(i, j) && i != j {
            self.num_edges += 1;
            self.graph.set(get_position(i, j), true);
        }
    }

    /// Removes the edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    /// }
    /// for i in 0..10
    /// {
    ///     g.remove_edge(i,i+1);
    ///     assert!(!g.is_edge(i,i+1));
    ///     assert!(g.size() == 10-i-1);
    /// }
    /// ```
    pub fn remove_edge(&mut self, i: usize, j: usize) {
        let n = self.order();
        if i < n && j < n && self.is_edge(i, j) && i != j {
            self.num_edges -= 1;
            self.graph.set(get_position(i, j), false);
        }
    }

    /// Returns an iterator over the vertices of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let g = graph::Graph::new(11);
    /// let mut i = 0;
    /// for n in g.vertices()
    /// {
    ///     assert!(n == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.order());
    /// ```
    pub fn vertices(&self) -> VertexIterator {
        VertexIterator::new(self.order())
    }

    /// Returns an iterator over the edges of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    /// }
    /// let mut i = 0;
    /// for e in g.edges()
    /// {
    ///     assert!(e.0 == i+1 && e.1 == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.size());
    /// ```
    pub fn edges(&self) -> EdgeIterator {
        EdgeIterator::new(&self)
    }

    /// Returns an iterator over the neighbors of the vertx v in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// let neighs = vec![2,6,8,9];
    /// for i in neighs.iter()
    /// {
    ///     g.add_edge(7,*i);
    /// }
    /// let mut i = 0;
    /// for u in g.neighbors(7)
    /// {
    ///     assert!(u == neighs[i]);
    ///     i += 1;
    /// }
    /// assert!(i == neighs.len());
    /// ```
    pub fn neighbors(&self, v: usize) -> NeighborIterator {
        NeighborIterator::new(v, &self)
    }
}

impl fmt::Debug for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}

impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}

/// Iterator over the vertices of the graph.
pub struct VertexIterator {
    n: usize,
    max: usize,
}

impl VertexIterator {
    fn new(max: usize) -> VertexIterator {
        VertexIterator { n: 0, max: max }
    }
}

impl Iterator for VertexIterator {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.n += 1;
        if self.n > self.max {
            None
        } else {
            Some(self.n - 1)
        }
    }
}

/// Iterator over the vertices of the graph.
pub struct EdgeIterator<'a> {
    u: usize,
    v: usize,
    c: usize,
    g: &'a Graph,
}

impl<'a> EdgeIterator<'a> {
    fn new(g: &Graph) -> EdgeIterator {
        EdgeIterator {
            u: 0,
            v: 0,
            c: 0,
            g: g,
        }
    }

    fn inc(&mut self) {
        self.u += 1;
        self.v += self.u / self.g.order();
        if self.u == self.g.order() {
            self.u = self.v + 1;
        }
    }
}

impl<'a> Iterator for EdgeIterator<'a> {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.g.order();
        if n == 0 {
            return None;
        }
        self.inc();
        let m = self.g.size();
        while self.v < n - 1 && self.c < m && !self.g.is_edge(self.u, self.v) {
            self.inc();
        }
        if self.c >= m || self.v >= n {
            None
        } else {
            self.c += 1;
            Some((self.u, self.v))
        }
    }
}

/// Iterator over the adjacent vertices of a given vertex in the graph.
///
/// This iterator goes through every vertex but only returns neighbors.
pub struct NeighborIterator<'a> {
    n: usize,
    u: usize,
    g: &'a Graph,
    first: bool,
}

impl<'a> NeighborIterator<'a> {
    fn new(n: usize, g: &Graph) -> NeighborIterator {
        NeighborIterator {
            n: n,
            u: 0,
            g: g,
            first: true,
        }
    }
}

impl<'a> Iterator for NeighborIterator<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.first {
            self.u += 1;
        } else {
            self.first = false;
        }
        let n = self.g.order();
        while self.u < n && !self.g.is_edge(self.u, self.n) {
            self.u += 1;
        }
        if self.u >= n { None } else { Some(self.u) }
    }
}

#[cfg(test)]
mod testing {
    use super::*;

    #[test]
    fn get_position_test() {
        assert!(get_position(1, 0) == 0);
        assert!(get_position(0, 1) == 0);
        assert!(get_position(0, 2) == 1);
    }
}
