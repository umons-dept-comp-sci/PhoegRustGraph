use graph::nauty::canon_graph;
use graph::GraphNauty;
use graph::{Graph, GraphIter};
use graph::transfo_result::GraphTransformation;
use graph::format;
use graph::transfos::remove_edge;

struct NaiveTransfo {
    n: u64,
    g: GraphNauty,
}

impl NaiveTransfo {
    fn new(g: &GraphNauty) -> Self {
        let n = g.order();
        let mut gt = GraphNauty::new(n*2);
        for i in 1..n {
            for j in 0..i {
                if g.is_edge(i, j) {
                    gt.add_edge(i, j);
                }
            }
        }
        NaiveTransfo {
            n: n,
            g: gt,
        }
    }

    fn add_edge(&mut self, i: u64, j: u64) {
        if !self.g.is_edge(i, j) {
            self.g.add_edge(i, j);
            if self.g.is_edge(i+self.n, j+self.n) {
                self.g.remove_edge(i+self.n, j+self.n);
            } else {
                self.g.add_edge(i+self.n, j+self.n);
            }
        }
    }

    fn remove_edge(&mut self, i: u64, j: u64) {
        if self.g.is_edge(i, j) {
            self.g.remove_edge(i, j);
            if self.g.is_edge(i+self.n, j+self.n) {
                self.g.remove_edge(i+self.n, j+self.n);
            } else {
                self.g.add_edge(i+self.n, j+self.n);
            }
        }
    }

    fn to_g6(&self) -> String {
        format::to_g6(&self.g)
    }

    fn cannon(&mut self) {
        let (g, _, _) = canon_graph(&self.g);
        self.g = g;
    }
}

fn main() {
    let mut g = GraphNauty::new(4);
    g.add_edge(0, 1);
    g.add_edge(1, 2);
    g.add_edge(2, 3);
    g.add_edge(3, 0);
    let mut vec = Vec::new();
    for i in 0..g.order() {
        for j in 0..g.order() {
            if i != j && g.is_edge(i, j) {
                let mut gt = NaiveTransfo::new(&g);
                gt.remove_edge(i, j);
                gt.cannon();
                vec.push(gt.to_g6());
            }
        }
    }
    vec.sort_unstable();
    let mut res = Vec::new();
    if vec.len() > 0 {
        let mut previous = &vec[0];
        res.push(previous);
        for i in 1..vec.len() {
            if &vec[i] != previous {
                previous = &vec[i];
                res.push(previous);
            }
        }
    }
    println!("{:?}", res);
    println!("{:?}", remove_edge(&g));
}
