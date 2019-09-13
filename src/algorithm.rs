use Graph;
use std::collections::VecDeque;

trait Visitor {
    fn visit(&mut self, g: &Graph, v: u64);
}

fn bfs<V>(g: &Graph, visitor: &mut V, start: Option<u64>)
    where V: Visitor
{
    if g.order() > 0 {
        let start = start.unwrap_or(0);
        let mut queue = VecDeque::new();
        queue.push_back(start);
        let mut visited = vec![false; g.order() as usize];
        visited[start as usize] = true;
        while !queue.is_empty() {
            let current = queue.pop_front().unwrap();
            if g.is_vertex(current) {
                visitor.visit(&g, current);
                for x in g.neighbors(current) {
                    if !visited[x as usize] {
                        visited[x as usize] = true;
                        queue.push_back(x);
                    }
                }
            }
        }
    }
}

struct VisitorConnected {
    num: u64,
}

impl VisitorConnected {
    fn is_connected(&self, g: &Graph) -> bool {
        self.num == g.order()
    }
}

impl Visitor for VisitorConnected {
    fn visit(&mut self, _: &Graph, _: u64) {
        self.num += 1;
    }
}

/// Tests whether the graph is connected. i.e., if each vertex can reach every other vertex.
/// # Examples :
/// ```
/// let mut g = graph::Graph::new(3);
/// for i in 0..2 {
///    for j in (i+1)..3 {
///         g.add_edge(i,j);
///    }
/// }
/// assert!(graph::algorithm::is_connected(&g));
/// g = graph::Graph::new(5);
/// assert!(!graph::algorithm::is_connected(&g));
/// g.add_cycle(&[0,1,2,3,4]);
/// assert!(graph::algorithm::is_connected(&g));
/// g.remove_edge(0,1);
/// assert!(graph::algorithm::is_connected(&g));
/// g.remove_edge(2,3);
/// assert!(!graph::algorithm::is_connected(&g));
/// ```
pub fn is_connected(g: &Graph) -> bool {
    let mut v = VisitorConnected { num: 0 };
    bfs(&g, &mut v, None);
    v.is_connected(&g)
}
