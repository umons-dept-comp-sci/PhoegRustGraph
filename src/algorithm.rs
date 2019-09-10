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
        while !queue.is_empty() {
            let current = queue.pop_front().unwrap();
            if g.is_vertex(current) {
                visitor.visit(&g, current);
                visited[current as usize] = true;
                for x in g.neighbors(current).filter(|&y| g.is_vertex(y) && !visited[y as usize]) {
                    queue.push_back(x);
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

pub fn is_connected(g: &Graph) -> bool {
    let mut v = VisitorConnected { num: 0 };
    bfs(&g,&mut v,None);
    v.is_connected(&g)
}
