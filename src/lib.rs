//#![feature(trace_macros)]
//#Crate using binary format to represent small graphs (order <= 11)

extern crate bit_vec;

pub mod format;
pub mod invariants;
pub mod errors;
pub mod nauty;
#[macro_use]
mod transfos_macros;
pub mod transfos;
pub mod subgraphs;

use std::fmt;
use std::ops::Range;

pub trait GraphTrait<'a> {
    /// A node in the graph
    type Vertex;
    /// An edge in the graph
    type Edge;

    /// An iterator over the vertices
    type Vertices: Iterator<Item = Self::Vertex>;

    /// An iterator over the edges
    type Edges: Iterator<Item = Self::Edge>;

    /// An iterator over the neighbors of a vertex
    type Neighbors: Iterator<Item = Self::Vertex>;

    /// Returns the order of the graph
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for _ in 0..11
    /// {
    ///     g.add_vertex();
    /// }
    /// assert!(g.order() == 11);
    /// ```
    fn order(&self) -> usize;

    /// Returns the size of the graph
    ///
    /// #Examples
    ///
    /// ```
    /// use graph::GraphTrait;
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
    fn size(&self) -> usize;

    /// Returns `true` if `x` is the index of a vertex.
    ///
    /// For a graph of order n, the indices should be between 0 and n-1.
    fn is_vertex(&self, x: usize) -> bool;

    /// Returns the `x`th vertex in the graph and `None` if there is no such vertex.
    ///
    /// For a graph of order n, the indices should be between 0 and n-1.
    fn get_vertex(&self, x: usize) -> Option<Self::Vertex>;

    /// Adds a new vertex to the graph, increasing its order by one.
    /// Will return false if the graph had already an order of 11.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for i in 0..11
    /// {
    ///     g.add_vertex();
    ///     assert!(g.order() == i+1);
    /// }
    /// ```
    fn add_vertex(&mut self);

    /// Removes the vertex i from the graph. The order if the vertices is not conserved.
    /// The last vertex takes the place of the removed one.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
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
    fn remove_vertex(&mut self, i: Self::Vertex);

    /// Checks weither the vertices i and j are adjacent.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    /// }
    /// assert!(!g.is_edge(10,0));
    /// ```
    fn is_edge(&self, i: usize, j: usize) -> bool;

    /// Returns the edge between the ith and jth vertices and `None` if they are not adjacent or if
    /// the do not exists.
    fn get_edge(&self, i: usize, j: usize) -> Option<Self::Edge>;

    /// Adds an edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    ///     assert!(g.size() == i+1);
    /// }
    /// ```
    fn add_edge(&mut self, i: usize, j: usize);

    /// Removes the edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
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
    fn remove_edge(&mut self, i: usize, j: usize);

    /// Returns an iterator over the vertices of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
    /// let g = graph::Graph::new(11);
    /// let mut i = 0;
    /// for n in g.vertices()
    /// {
    ///     assert!(n == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.order());
    /// ```
    fn vertices(&self) -> Self::Vertices;

    /// Returns an iterator over the edges of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
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
    fn edges(&'a self) -> Self::Edges;

    /// Returns an iterator over the neighbors of the vertx v in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::GraphTrait;
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
    fn neighbors(&self, v: usize) -> <Graph as GraphTrait>::Neighbors;
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
}

impl<'a> GraphTrait<'a> for Graph {
    type Vertex = usize;
    type Edge = (usize, usize);
    type Vertices = Range<Self::Vertex>;
    type Edges = EdgeIterator<'a, Self>;
    type Neighbors = NeighborIterator<'a, Self>;

    fn order(&self) -> usize {
        self.num_vertices
    }

    fn size(&self) -> usize {
        self.num_edges
    }

    fn is_vertex(&self, n: usize) -> bool {
        self.get_vertex(n).is_some()
    }

    fn get_vertex(&self, n: usize) -> Option<Self::Vertex> {
        if n < self.order() { Some(n) } else { None }
    }

    fn add_vertex(&mut self) {
        self.num_vertices += 1;
        self.graph.grow(self.num_vertices, false);
    }

    // [TODO]: Add unit tests for this.
    fn remove_vertex(&mut self, i: usize) {
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

    fn is_edge(&self, i: usize, j: usize) -> bool {
        let n = self.order();
        i < n && j < n && i != j && (self.graph.get(get_position(i, j)).unwrap())
    }

    fn get_edge(&self, i: Self::Vertex, j: Self::Vertex) -> Option<Self::Edge> {
        if self.is_edge(i, j) {
            Some((i, j))
        } else {
            None
        }
    }


    fn add_edge(&mut self, i: usize, j: usize) {
        let n = self.order();
        if i < n && j < n && !self.is_edge(i, j) && i != j {
            self.num_edges += 1;
            self.graph.set(get_position(i, j), true);
        }
    }

    fn remove_edge(&mut self, i: usize, j: usize) {
        let n = self.order();
        if i < n && j < n && self.is_edge(i, j) && i != j {
            self.num_edges -= 1;
            self.graph.set(get_position(i, j), false);
        }
    }

    fn vertices(&self) -> <Graph as GraphTrait>::Vertices {
        (0..self.order())
    }

    fn edges(&'a self) -> <Graph as GraphTrait<'a>>::Edges {
        EdgeIterator::new(&self)
    }

    fn neighbors(&self, v: usize) -> <Graph as GraphTrait>::Neighbors {
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
pub struct EdgeIterator<'a, G>
    where G: GraphTrait<'a> + 'a
{
    u: usize,
    v: usize,
    c: usize,
    g: &'a G,
}

impl<'a, G> EdgeIterator<'a, G>
    where G: GraphTrait<'a> + 'a
{
    fn new(g: &'a G) -> EdgeIterator<'a, G> {
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

impl<'a, G> Iterator for EdgeIterator<'a, G>
    where G: GraphTrait<'a>
{
    type Item = G::Edge;

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
            self.g.get_edge(self.u, self.v)
        }
    }
}

/// Iterator over the adjacent vertices of a given vertex in the graph.
///
/// This iterator goes through every vertex but only returns neighbors.
pub struct NeighborIterator<'a, G>
    where G: GraphTrait<'a> + 'a
{
    n: usize,
    u: usize,
    g: &'a G,
    first: bool,
}

impl<'a, G> NeighborIterator<'a, G>
    where G: GraphTrait<'a>
{
    fn new(n: usize, g: &'a G) -> NeighborIterator<'a, G> {
        NeighborIterator {
            n: n,
            u: 0,
            g: g,
            first: true,
        }
    }
}

impl<'a, G> Iterator for NeighborIterator<'a, G>
    where G: GraphTrait<'a>
{
    type Item = G::Vertex;

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
        if self.u >= n {
            None
        } else {
            self.g.get_vertex(self.u)
        }
    }
}

#[cfg(test)]
mod testing {
    use super::*;
    use std::iter::repeat;

    #[test]
    fn get_position_test() {
        assert!(get_position(1, 0) == 0);
        assert!(get_position(0, 1) == 0);
        assert!(get_position(0, 2) == 1);
    }

    #[test]
    fn test_iterate_over_edges() {
        let mut g = Graph::new(7);
        for (x, y) in g.vertices().skip(1).zip(g.vertices().take(6)) {
            g.add_edge(x, y);
        }
        for i in g.vertices()
            .enumerate()
            .skip(1)
            .flat_map(|(x, y)| repeat(y).zip(g.vertices().take(x)))
            .filter_map(|(x, y)| g.get_edge(x, y)) {
            println!("{:?}", i);
        }
        panic!();
    }
}
