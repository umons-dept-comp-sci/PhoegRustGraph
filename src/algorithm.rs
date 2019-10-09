use std::collections::VecDeque;
use transfo_result::GraphTransformation;
use Graph;

pub trait Visitor {
    fn visit_vertex(&mut self, g: &Graph, u: u64);
    fn visit_edge(&mut self, g: &Graph, u: u64, v: u64);
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

fn visit<V, Q>(g: &Graph, visitor: &mut V, queue: &mut Q, start: Option<u64>)
where
    V: Visitor,
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
                visitor.visit_vertex(&g, current);
                for x in g.neighbors(current) {
                    visitor.visit_edge(&g, current, x);
                    if !visited[x as usize] {
                        visited[x as usize] = true;
                        queue.enqueue(x);
                    }
                }
            }
        }
    }
}

pub fn bfs<V>(g: &Graph, visitor: &mut V, start: Option<u64>)
where
    V: Visitor,
{
    let mut queue = VecDeque::new();
    visit(g, visitor, &mut queue, start);
}

pub fn dfs<V>(g: &Graph, visitor: &mut V, start: Option<u64>)
where
    V: Visitor,
{
    let mut queue = Fifo { v: VecDeque::new() };
    visit(g, visitor, &mut queue, start);
}

// TODO test
/// Remove all edges containing u.
pub fn isolate(g: &mut Graph, u: u64) {
    for x in g.neighbors(u) {
        g.remove_edge(u, x);
    }
}

// TODO test
/// Remove all edges containing u.
pub fn isolate_transfo(g: &mut GraphTransformation, u: u64) {
    for x in 0..=g.max_vertex() {
        if g.is_vertex(x) && g.is_edge(u, x) {
            g.remove_edge(u, x);
        }
    }
}

// TODO test
/// Tests whether every neighbor of u is a neighbor of v.
pub fn has_neighborhood_included(g: &Graph, u: u64, v: u64) -> bool {
    let mut i = 0;
    for x in g.neighbors(u).filter(|x| *x != v) {
        if !g.is_edge(x, v) {
            return false;
        }
        i += 1;
    }
    i > 0
}
