use std::collections::{HashSet, VecDeque};
use std::collections::hash_set::Iter;
use std::iter::FromIterator;
use crate::transfo_result::GraphTransformation;
use crate::Graph;
use crate::GraphIter;

pub trait Visitor<G: Graph> {
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

pub fn bfs<'a, G, V>(g: &'a G, visitor: &mut V, start: Option<u64>)
    where
        V: Visitor<G>,
        G: Graph + GraphIter<'a>,
{
    let mut queue = VecDeque::new();
    visit(g, visitor, &mut queue, start);
}

pub fn dfs<'a, G, V>(g: &'a G, visitor: &mut V, start: Option<u64>)
    where
        G: Graph + GraphIter<'a>,
        V: Visitor<G>,
{
    let mut queue = Fifo { v: VecDeque::new() };
    visit(g, visitor, &mut queue, start);
}

/// Remove all edges containing u.
/// # Examples:
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
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
pub fn isolate<'a, G>(g: &mut G, u: u64)
    where G: GraphIter<'a>
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


pub struct CliquesIterator<'a, G>
    where G: Graph + GraphIter<'a>
{
    g: &'a G,
    // u64 should be something like Graph::index_type
    q: Vec<u64>,
    // Cache the adjacency sets as in NetworkX implementation of Bron-Kerbosch.
    // TODO: benchmark HashSet vs BTreeSet.
    adj: Vec<HashSet<u64>>,
    // Stack used to unroll the recursive algorithm arguments and state.
    // A stack frame represents (subg, cand, partial (cand - adj[u])).
    stack: Vec<(HashSet<u64>, HashSet<u64>, Vec<u64>)>,
}

impl<'a, G> CliquesIterator<'a, G>
    where G: Graph + GraphIter<'a>
{
    fn new(g: &'a G, q: Vec<u64>, subg: HashSet<u64>, cand: HashSet<u64>)
           -> CliquesIterator<'a, G> {
        let mut adj = Vec::<HashSet<u64>>::with_capacity(
            g.order() as usize);
        for v in 0..g.order() {
            adj.push(HashSet::<u64>::from_iter(g.neighbors(v)));
        }
        let u = subg.iter().cloned().max_by_key(
            |u| (&cand & &adj[*u as usize]).len()).unwrap();
        let ext_u = Vec::from_iter(&cand - &adj[u as usize]);
        let stack = vec![(subg, cand, ext_u)];
        return CliquesIterator { g, q, adj, stack };
    }
}

impl<'a, G> Iterator for CliquesIterator<'a, G>
    where G: Graph + GraphIter<'a>
{
    // FIXME: if we agree to invalidate the cliques vectors between each
    //   iteration step, we may return a ref here and avoid potentially useless
    //   copies?
    type Item = Vec<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        // Fetch recursive-loop-unrolled stack frames.
        loop
        {
            if self.stack.is_empty() {
                // Search finished, all pseudo-recursive calls have returned.
                return None;
            }
            // Take a peek at the frame.
            let (ref subg,
                ref mut cand,
                ref mut ext_u) = self.stack.last_mut().unwrap();
            match ext_u.pop() {
                None => {
                    // We have expanded all vertices of cand - adj[u].
                    // We can pop this frame.
                    self.stack.pop();
                    // Last instruction after the recursive call was to pop q.
                    self.q.pop();
                }
                // We're in the for loop, iterating over cand - adj[u].
                Some(p) => {
                    self.q.push(p);
                    cand.remove(&p);
                    let adj_p = &self.adj[p as usize];
                    let subg_p = subg & adj_p;
                    // Unroll the first instructions of the recursive call here.
                    if subg_p.is_empty() {
                        // q is a maximal clique.
                        // FIXME: it annoys me that we necessarily copy q here.
                        //  If we only want to count the number of cliques, this
                        //  is wasting resources.
                        let ret = Some(self.q.clone());
                        self.q.pop();
                        return ret;
                    } else {
                        let cand_p = adj_p & cand;
                        // FIXME: should we cut if cand_p is empty ?
                        // prepare the "for p in cand - adj[u]" loop of the
                        // recursive call. That is: add the corresponding frame
                        // on the stack.
                        let adj = &self.adj;
                        let u = subg_p.iter().cloned().max_by_key(
                            |u| (&cand_p & &adj[*u as usize])
                                .len()).unwrap();
                        let ext_u_p = Vec::from_iter(
                            &cand_p - &self.adj[u as usize]);
                        self.stack.push((subg_p, cand_p, ext_u_p));
                    }
                }
            }
        }
    }
}

/// Iterate over the maximal cliques of the graph.
/// TODO: add support for an optional argument specifying a set of nodes to
/// expand (iterate on the max cliques containing the given set of vertices).
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::algorithm::cliques;
/// use std::collections::{BTreeSet};
/// use std::iter::FromIterator;
///
/// let mut g = GraphNauty::new(9);
/// g.add_edges_from([
///     (0, 1), (0, 8),
///     (1, 2), (1, 8),
///     (2, 3), (2, 7), (2, 8),
///     (3, 4), (3, 5), (3, 6), (3, 7),
///     (4, 5),
///     (5, 6), (5, 7),
///     (6, 7),
/// ]);
/// let expected: Vec<Vec<u64>> = vec![
///     vec![3, 5, 6, 7],
///     vec![3, 5, 4],
///     vec![3, 2, 7],
///     vec![0, 1, 8],
///     vec![1, 2, 8]];
///
/// let g_cliques: Vec<Vec<u64>> = cliques(&g).collect();
/// // FIXME: factor that.
/// let g_cliques_sets: BTreeSet<BTreeSet<u64>> = BTreeSet::from_iter(
///     g_cliques.iter().map(
///         |clique|
///             BTreeSet::from_iter(clique.iter().cloned())));
/// let expected_cliques_set: BTreeSet<BTreeSet<u64>> = BTreeSet::from_iter(
///     expected.iter().map(
///         |clique|
///             BTreeSet::from_iter(clique.iter().cloned())));
/// assert_eq!(
///     g_cliques_sets, expected_cliques_set,
///     concat!("testing if the set of cliques matches",
///     " (left: result, right: expected)")
/// );
/// ```
pub fn cliques<'a, G>(g: &'a G) -> CliquesIterator<'a, G>
    where G: Graph + GraphIter<'a>
{
    let subg = HashSet::from_iter(0..g.order());
    let cand = subg.clone();
    return CliquesIterator::new(g, vec![], subg, cand);
}