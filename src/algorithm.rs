use std::collections::VecDeque;
use crate::transfo_result::GraphTransformation;
use crate::Graph;
use crate::GraphIter;

pub trait Visitor<G:Graph> {
    fn visit_vertex(&mut self, g: &G, u: u64);
    fn visit_edge(&mut self, g: &G, u: u64, v: u64);
}

trait Queue {
    fn enqueue(&mut self, u: u64);
    fn dequeue(&mut self) -> u64;
    fn is_empty(&self) -> bool;
}

impl Queue for VecDeque<u64> {
    fn enqueue(&mut self, u: u64) {
        self.push_back(u);
    }

    fn dequeue(&mut self) -> u64 {
        self.pop_front().unwrap()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

struct Fifo {
    v: VecDeque<u64>,
}

impl Queue for Fifo {
    fn enqueue(&mut self, u: u64) {
        self.v.push_back(u);
    }

    fn dequeue(&mut self) -> u64 {
        self.v.pop_front().unwrap()
    }

    fn is_empty(&self) -> bool {
        self.v.is_empty()
    }
}

fn visit<'a, G, V, Q>(g: &'a G, visitor: &mut V, queue: &mut Q, start: Option<u64>)
where
    G: GraphIter,
    V: Visitor<G>,
    Q: Queue,
{
    if g.order() > 0 {
        let start = start.unwrap_or(0);
        queue.enqueue(start);
        let mut visited = vec![false; g.order() as usize];
        visited[start as usize] = true;
        while !queue.is_empty() {
            let current = queue.dequeue();
            if g.is_vertex(current) {
                visitor.visit_vertex(g, current);
                for x in g.neighbors(current) {
                    visitor.visit_edge(g, current, x);
                    if !visited[x as usize] {
                        visited[x as usize] = true;
                        queue.enqueue(x);
                    }
                }
            }
        }
    }
}

pub fn bfs<'a,G,V>(g: &'a G, visitor: &mut V, start: Option<u64>)
where
    V: Visitor<G>,
    G: Graph+GraphIter,
{
    let mut queue = VecDeque::new();
    visit(g, visitor, &mut queue, start);
}

pub fn dfs<'a,G,V>(g: &'a G, visitor: &mut V, start: Option<u64>)
where
    G:Graph+GraphIter,
    V: Visitor<G>,
{
    let mut queue = Fifo { v: VecDeque::new() };
    visit(g, visitor, &mut queue, start);
}

/// Remove all edges containing u.
/// # Examples:
/// ```
/// use graph::{Graph,GraphNauty};
/// use graph::algorithm::isolate;
/// let mut g = GraphNauty::new(5);
/// for i in 0..4 {
///     for j in i..5 {
///         g.add_edge(i,j);
///     }
/// }
/// isolate(&mut g, 2);
/// for i in 0..5 {
///     assert!(!g.is_edge(2,i));
/// }
/// g.add_edge(2,3);
/// isolate(&mut g, 3);
/// for i in 0..5 {
///     assert!(!g.is_edge(3,i));
/// }
/// ```
pub fn isolate<'a,G>(g: &mut G, u: u64)
    where G:GraphIter
{
    for x in g.neighbors(u) {
        g.remove_edge(u, x);
    }
}

// TODO test or merge it with isolate for graphs
/// Remove all edges containing u.
pub fn isolate_transfo(g: &mut GraphTransformation, u: u64) {
    for x in 0..=g.max_vertex() {
        if g.is_vertex(x) && g.is_edge(u, x) {
            g.remove_edge(u, x);
        }
    }
}

/// Tests whether every neighbor of u is a neighbor of v.
///
/// # Examples:
/// ```
/// use graph::{Graph,GraphNauty, algorithm::has_neighborhood_included};
/// let mut g = GraphNauty::new(5);
/// for i in 0..4 {
///     for j in i..5 {
///         g.add_edge(i,j);
///     }
/// }
/// assert!(has_neighborhood_included(&g,0,1));
/// g.remove_edge(0,2);
/// assert!(has_neighborhood_included(&g,0,1));
/// g.remove_edge(1,3);
/// assert!(!has_neighborhood_included(&g,0,1));
/// ```
pub fn has_neighborhood_included<'a, G>(g: &'a G, u: u64, v: u64) -> bool
    where G:GraphIter
{
    let mut i = 0;
    for x in g.neighbors(u).filter(|x| *x != v) {
        if !g.is_edge(x, v) {
            return false;
        }
        i += 1;
    }
    i > 0
}
