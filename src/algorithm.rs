use std::collections::VecDeque;
use crate::transfo_result::GraphTransformation;
use crate::Graph;
use crate::GraphIter;
use crate::GraphNauty;

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
    G: GraphIter<'a>,
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
    G: Graph+GraphIter<'a>,
{
    let mut queue = VecDeque::new();
    visit(g, visitor, &mut queue, start);
}

pub fn dfs<'a,G,V>(g: &'a G, visitor: &mut V, start: Option<u64>)
where
    G:Graph+GraphIter<'a>,
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
    where G:GraphIter<'a>
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

pub fn karger_mincut(g: &mut GraphNauty) -> (u64,u64)
{
    use rand::Rng;

    //println!{"graph : {:?}",g};

    //println!("Graphe avant karger {:?}",g);

    let mut best_minimum_cut_edges = Vec::new();
    let mut best_minimum_cut = g.order();

    for i in 0..10{
        let graph_copy = g.clone();

        let mut vertices_correspondance = Vec::new();
        
        for v in g.vertices(){
            let mut vertices = Vec::new();
            vertices.push(v);
            vertices_correspondance.push(vertices);
        }

        while(g.order() > 2){
            let degrees: Vec<u64> = g.vertices()    
            .map(|x| g.neighbors(x).count() as u64)
            .collect();

            let num = rand::thread_rng().gen_range(0..g.size()*2);

            let mut deg = 0;
            let mut vertex = 0;
            for degree in &degrees{
                if(num < deg + degree){
                    break;
                }
                deg += *degree;
                vertex += 1;
            }

            //println!("{:?} {:?} {:?} {:?}",num,deg,degrees,g.size()*2);

            let u = vertex;
            let v = g.neighbors(vertex).nth((num - deg) as usize).unwrap();

            if(u > v){
                let (u,v) = (v,u);
            }

            for n in g.neighbors(v){
                if(u != n){
                    g.add_edge(u,n);
                }
            }
            
            let mut to_add = Vec::new();
            let v_correspondance = &vertices_correspondance[v as usize];
            for c in v_correspondance{
                to_add.push(*c);
            }
            vertices_correspondance[u as usize].append(&mut to_add);
            vertices_correspondance.remove(v as usize);

            g.remove_vertex(v);
        }

        //println!("Graphe après karger {:?}",g);

        *g = graph_copy;

        let mut minimum_cut = 0;
        let mut minimum_cut_edges = Vec::new();

        for u in &vertices_correspondance[0]{
            for v in &vertices_correspondance[1]{
                if g.is_edge(*u,*v){
                    //println!("Chosen edge : {} {}",*u,*v);
                    minimum_cut +=1;
                    if(u > v){
                        minimum_cut_edges.push((*v,*u));
                    }
                    else{
                        minimum_cut_edges.push((*u,*v));
                    }
                }
            }
        }

        //println!("minimum cut : {} {:?} {:?} {:?}",minimum_cut,minimum_cut_edges,g,vertices_correspondance);

        if minimum_cut < best_minimum_cut{
            best_minimum_cut = minimum_cut;
            best_minimum_cut_edges = minimum_cut_edges;
        }
    }

    //println!("vertices correspondance : {:?}",vertices_correspondance);

    //println!("{:?}",best_minimum_cut_edges);
    best_minimum_cut_edges[0]
}
