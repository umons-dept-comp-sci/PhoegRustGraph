//! Module containing implementations of different graph invariants

use crate::Graph;
use crate::GraphIter;
use crate::algorithm::{bfs, dfs, Visitor, cliques};
use crate::errors::*;
use std::f64;
use std::u64::MAX;

///
/// Represents distances that can be infinite.
/// # Examples
///
/// ```
/// use graph::{Graph,GraphNauty};
/// use graph::invariants::Distance;
/// let a = Distance::Val(1);
/// let b = Distance::Val(2);
/// let c = a + b;
/// if let Distance::Val(v) = c {
///     assert!(v == 3);
/// } else {
///     assert!(false);
/// }
/// assert!(a < Distance::Inf);
/// ```
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub enum Distance {
    /// Infinite distance
    Inf,
    /// Finite distance
    Val(u64),
}

impl Distance {
    /// Returns the value of a finite distance and None if the distance was infinite.
    ///
    /// # Examples
    /// ```
    /// use graph::invariants::Distance;
    /// assert!(Distance::Val(6).get_val().is_some());
    /// assert!(Distance::Inf.get_val().is_none());
    /// ```
    pub fn get_val(&self) -> Option<u64> {
        match *self {
            Distance::Inf => None,
            Distance::Val(x) => Some(x),
        }
    }

    /// Returns `true` if the value is finite and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::invariants::Distance;
    /// assert!(Distance::Val(42).is_finite());
    /// assert!(!Distance::Inf.is_finite());
    /// ```
    pub fn is_finite(&self) -> bool {
        match *self {
            Distance::Val(_) => true,
            Distance::Inf => false,
        }
    }

    /// Returns `true` if the value is infinite and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::invariants::Distance;
    /// assert!(Distance::Inf.is_infinite());
    /// assert!(!Distance::Val(42).is_infinite());
    /// ```
    pub fn is_infinite(&self) -> bool {
        !self.is_finite()
    }
}

impl std::fmt::Display for Distance {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            Distance::Val(x) => write!(f, "{}", x),
            Distance::Inf => write!(f, "Inf"),
        }
    }
}

impl ::std::ops::Add for Distance {
    type Output = Distance;

    fn add(self, other: Distance) -> Distance {
        match (self, other) {
            (Distance::Val(v), Distance::Val(o)) => Distance::Val(o + v),
            _ => Distance::Inf,
        }
    }
}

impl ::std::cmp::PartialEq for Distance {
    fn eq(&self, other: &Distance) -> bool {
        match (self, other) {
            (&Distance::Val(v), &Distance::Val(o)) => o == v,
            (&Distance::Inf, &Distance::Inf) => true,
            _ => false,
        }
    }
}

impl ::std::cmp::PartialOrd for Distance {
    fn partial_cmp(&self, other: &Distance) -> Option<::std::cmp::Ordering> {
        use std::cmp::Ordering;
        match (self, other) {
            (&Distance::Val(v), &Distance::Val(o)) => Some(v.cmp(&o)),
            (&Distance::Inf, &Distance::Val(_)) => Some(Ordering::Greater),
            (&Distance::Val(_), &Distance::Inf) => Some(Ordering::Less),
            _ => Some(Ordering::Equal),
        }
    }
}

impl ::std::cmp::Eq for Distance {}

impl ::std::cmp::Ord for Distance {
    fn cmp(&self, other: &Distance) -> ::std::cmp::Ordering {
        use std::cmp::Ordering;
        match (self, other) {
            (&Distance::Val(v), &Distance::Val(o)) => v.cmp(&o),
            (&Distance::Inf, &Distance::Val(_)) => Ordering::Greater,
            (&Distance::Val(_), &Distance::Inf) => Ordering::Less,
            _ => Ordering::Equal,
        }
    }
}

/// Implementation of the floyd-warshall algorithm.
/// `u64::MAX` is used to represent infinity.
///
/// # Examples
///
/// ```
/// use std::u64::MAX;
/// use graph::{Graph,GraphConstructible,GraphNauty,GraphIter};
/// use graph::invariants::floyd_warshall;
/// use graph::invariants::Distance::{Val,Inf};
///
/// fn to_u64(v: Vec<Vec<graph::invariants::Distance>>) -> Vec<Vec<u64>>
/// {
///     v.iter().map(|x| x.iter().map(|x| match x {&Val(v) => v, &Inf => MAX}).collect()).collect()
/// }
///
/// let mut g = GraphNauty::new(0);
/// let distances: Vec<Vec<u64>> = to_u64(floyd_warshall(&g));
/// assert!(distances.len() == 0);
/// g.add_vertex();
/// let distances: Vec<Vec<u64>> = to_u64(floyd_warshall(&g));
/// assert!(distances.len() == 1);
/// assert!(distances[0].len() == 1);
/// assert!(distances[0][0] == 0);
/// for _ in 1..11
/// {
///     g.add_vertex();
/// }
/// for u in 1..10
/// {
///     g.add_edge(u-1,u);
/// }
/// let distances: Vec<Vec<u64>> = to_u64(floyd_warshall(&g));
/// let expected_distances = vec![vec![0,1,2,3,4,5,6,7,8,9,MAX],
///                               vec![1,0,1,2,3,4,5,6,7,8,MAX],
///                               vec![2,1,0,1,2,3,4,5,6,7,MAX],
///                               vec![3,2,1,0,1,2,3,4,5,6,MAX],
///                               vec![4,3,2,1,0,1,2,3,4,5,MAX],
///                               vec![5,4,3,2,1,0,1,2,3,4,MAX],
///                               vec![6,5,4,3,2,1,0,1,2,3,MAX],
///                               vec![7,6,5,4,3,2,1,0,1,2,MAX],
///                               vec![8,7,6,5,4,3,2,1,0,1,MAX],
///                               vec![9,8,7,6,5,4,3,2,1,0,MAX],
///                               vec![MAX,MAX,MAX,MAX,MAX,MAX,MAX,MAX,MAX,MAX,0]];
/// for u in g.vertices().map(|x| x as usize)
/// {
///     for v in g.vertices().map(|x| x as usize)
///     {
///         assert!(distances[u][v] == expected_distances[u][v]);
///     }
/// }
/// ```
pub fn floyd_warshall<'a, G>(g: &'a G) -> Vec<Vec<Distance>>
    where G: GraphIter<'a>
{
    use self::Distance::{Inf, Val};
    let n = g.order() as usize;
    let mut matrix = vec![vec![Inf; n]; n];
    for u in g.vertices().map(|x| x as usize) {
        matrix[u][u] = Val(0);
    }
    let mut verts = g.vertices();
    while let Some(u) = verts.next() {
        let mut verts2 = verts.clone();
        while let Some(v) = verts2.next() {
            if g.is_edge(u,v) {
                matrix[u as usize][v as usize] = Val(1);
                matrix[v as usize][u as usize] = Val(1);
            }
        }
    }
    for k in g.vertices().map(|x| x as usize) {
        for u in g.vertices().map(|x| x as usize) {
            for v in g.vertices().map(|x| x as usize) {
                if matrix[u][v] > matrix[u][k] + matrix[k][v] {
                    matrix[u][v] = matrix[u][k] + matrix[k][v];
                }
            }
        }
    }
    matrix
}

/// Returns the length of the longest shortest path in the graph.
/// This can also be defined as the maximum excentricity.
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty,GraphIter};
/// use graph::invariants::{Distance,diameter};
///
/// let mut g = GraphNauty::new(5);
/// assert!(diameter(&g).is_infinite());
/// for i in g.vertices().skip(1) {
///     g.add_edge(i-1,i);
/// }
/// let mut diam = diameter(&g);
/// assert!(diam.is_finite());
/// assert_eq!(diam.get_val().unwrap(),4);
/// for i in g.vertices().skip(1) {
///     for j in g.vertices().take(i as usize) {
///         g.add_edge(j,i);
///     }
/// }
/// diam = diameter(&g);
/// assert!(diam.is_finite());
/// assert_eq!(diam.get_val().unwrap(),1);
/// ```
pub fn diameter<'a, G>(g: &'a G) -> Distance
    where G: GraphIter<'a>
{
    if g.order() > 0 {
        let distances = floyd_warshall(g);
        *distances.iter()
            .map(|x| x.iter().max().unwrap())
            .max()
            .unwrap()
    } else {
        Distance::Inf
    }
}

struct AllPathsVisitor {
    dists: Vec<Distance>,
    paths: Vec<Vec<u64>>,
}

impl<G: Graph> Visitor<G> for AllPathsVisitor {
    fn visit_vertex(&mut self, _: &G, _: u64) {}

    fn visit_edge(&mut self, _: &G, u: u64, v: u64) {
        let cdist = self.dists[u as usize] + Distance::Val(1);
        let ndist = self.dists[v as usize];
        // ndist was infinite (we know it because it is a bfs)
        if ndist > cdist {
            self.dists[v as usize] = cdist;
            self.paths[v as usize].clear();
            self.paths[v as usize].push(u);
            // there is another shortest path to join n
        } else if ndist == cdist {
            self.paths[v as usize].push(u);
        }
    }
}

/// Returns all the shortests paths from `start`.
///
///  # Examples
///
///  ```
///  use graph::GraphNauty;
///  use graph::invariants::{shortest_paths_from, Distance};
///  use graph::format::from_g6;
///
///  let g: GraphNauty = from_g6(&String::from("GiGoG?")).unwrap();
///  let res = shortest_paths_from(&g,0);
///  let dists : Vec<Distance> = [0,1,2,2,3,3,4].iter().map(|&x|
///  Distance::Val(x)).chain([Distance::Inf].iter().cloned()).collect();
///  let paths = vec![vec![],vec![0],vec![1],vec![1],vec![2],vec![2,3],vec![5],vec![]];
///  assert_eq!(res.0.len(),dists.len());
///  for v in res.0.iter().enumerate() {
///     assert_eq!(*v.1, dists[v.0]);
///  }
///  assert_eq!(res.1.len(),paths.len());
///  for p in paths.iter().enumerate() {
///     let i = p.0;
///     assert_eq!(p.1.len(),paths[i].len());
///     for e in p.1.iter().enumerate() {
///         let j = e.0;
///         assert_eq!(*e.1, paths[i][j]);
///     }
///  }
///  ```
pub fn shortest_paths_from<'a, G>(g: &'a G, start: u64) -> (Vec<Distance>, Vec<Vec<u64>>)
    where G: GraphIter<'a>
{
    let mut dists: Vec<Distance> = vec![Distance::Inf; g.order() as usize];
    let paths: Vec<Vec<u64>> = vec![Vec::new(); g.order() as usize];
    dists[start as usize] = Distance::Val(0);
    let mut v = AllPathsVisitor {
        dists: dists,
        paths: paths,
    };
    bfs(g, &mut v, Some(start));
    (v.dists, v.paths)
}

/// Computes the eccentricities of the graph
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphNauty};
/// use graph::invariants::{eccentricities, Distance};
/// use graph::format::from_g6;
///
/// let g: GraphNauty = from_g6(&String::from("FiGoG")).unwrap();
/// let r = eccentricities(&g);
/// let expected:Vec<Distance> = [4,3,2,3,3,3,4].iter().map(|&x| Distance::Val(x)).collect();
/// assert_eq!(r.len(), expected.len());
/// for (i,e) in r.iter().enumerate() {
///     assert_eq!(*e,expected[i]);
/// }
/// ```
pub fn eccentricities<'a, G>(g: &'a G) -> Vec<Distance>
    where G: GraphIter<'a>
{
    floyd_warshall(g)
        .iter()
        .map(|x| *x.iter().max().unwrap())
        .collect()
}

fn construct_paths(pths: &[Vec<u64>], s: u64, e: u64) -> Vec<Vec<u64>> {
    let mut res = vec![];
    if pths[e as usize].is_empty() || s == e {
        res.push(vec![e]);
        res
    } else {
        for &t in &pths[e as usize] {
            let tres = construct_paths(pths, s, t);
            for mut p in tres {
                p.push(e);
                res.push(p);
            }
        }
        res
    }
}

/// Returns the list of all elementary paths in g whose length is maximal.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphNauty};
/// use graph::invariants::{diametral_paths, Distance};
/// use graph::format::from_g6;
///
/// let g: GraphNauty = from_g6(&String::from("FiGoG")).unwrap();
/// let r = diametral_paths(&g);
/// let expected = vec![
///     vec![0,1,2,5,6],
///     vec![0,1,3,5,6],
///     vec![6,5,2,1,0],
///     vec![6,5,3,1,0]
///     ];
/// for (p1,p2) in r.iter().zip(expected.iter()) {
///     for (n1,n2) in p1.iter().zip(p2.iter()) {
///         assert_eq!(n1,n2);
///     }
/// }
/// ```
pub fn diametral_paths<'a, G>(g: &'a G) -> Vec<Vec<u64>>
    where G: GraphIter<'a>
{
    let eccs = eccentricities(g);
    let diam = eccs.iter().max().unwrap();
    let extms: Vec<u64> = (0..g.order())
        .filter(|&x| eccs[x as usize] == *diam)
        .collect();
    let mut res = vec![];
    for e in extms {
        let (dsts, pths) = shortest_paths_from(g, e);
        for (i, _dst) in dsts.iter().enumerate().filter(|&(_x, y)| y == diam) {
            let mut tres = construct_paths(&pths, e, i as u64);
            res.append(&mut tres);
        }
    }
    res
}

struct ComponentVisitor<'a> {
    verts: Vec<u64>,
    visited: &'a mut Vec<bool>,
}

impl<'a, G: Graph> Visitor<G> for ComponentVisitor<'a> {
    fn visit_vertex(&mut self, _: &G, v: u64) {
        self.verts.push(v);
        self.visited[v as usize] = true;
    }

    fn visit_edge(&mut self, _: &G, _: u64, _: u64) {}
}

fn connected_component_with<'a, G>(g: &'a G, u: u64, visited: &mut Vec<bool>) -> Vec<u64>
    where G: GraphIter<'a>
{
    let mut visitor = ComponentVisitor {
        verts: Vec::new(),
        visited: visited,
    };
    dfs(g, &mut visitor, Some(u));
    visitor.verts
}

/// Returns the connected components of the graph.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::connected_components;
/// let mut g = GraphNauty::new(0);
/// assert!(connected_components(&g).len() == 0);
/// for _ in 0..10
/// {
///     g.add_vertex();
/// }
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
///     g.add_edge(i+5,i+6);
/// }
/// g.add_edge(4,0);
/// g.add_edge(9,5);
/// let comps = connected_components(&g);
/// assert!(comps.len() == 2);
/// assert!(comps[0].len() == 5);
/// assert!(comps[1].len() == 5);
/// ```
pub fn connected_components<'a, G>(g: &'a G) -> Vec<Vec<u64>>
    where G: GraphIter<'a>
{
    let mut comps = vec![];
    let mut visited = vec![false; g.order() as usize];
    for u in g.vertices() {
        if !visited[u as usize] {
            comps.push(connected_component_with(g, u, &mut visited));
        }
    }
    comps
}

/// Tests whether the graph is connected. i.e., if each vertex can reach every other vertex.
/// # Examples :
/// ```
/// use graph::{Graph,GraphConstructible};
/// use graph::invariants::is_connected;
/// let mut g = graph::GraphNauty::new(3);
/// for i in 0..2 {
///    for j in (i+1)..3 {
///         g.add_edge(i,j);
///    }
/// }
/// assert!(is_connected(&g));
/// g = graph::GraphNauty::new(5);
/// assert!(!is_connected(&g));
/// g.add_cycle(&[0,1,2,3,4]);
/// assert!(is_connected(&g));
/// g.remove_edge(0,1);
/// assert!(is_connected(&g));
/// g.remove_edge(2,3);
/// assert!(!is_connected(&g));
/// ```
pub fn is_connected<'a, G>(g: &'a G) -> bool
    where G: GraphIter<'a>
{
    let mut vis = vec![false; g.order() as usize];
    let mut v = ComponentVisitor {
        verts: Vec::new(),
        visited: &mut vis,
    };
    bfs(g, &mut v, None);
    v.verts.len() == g.order() as usize
}

fn shortests_paths_length(p: &[Vec<u64>]) -> u64 {
    if !p.is_empty() {
        p[0].len() as u64 - 1
    } else {
        MAX
    }
}

fn combine_paths(p1: &[Vec<u64>], p2: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let mut res = vec![];
    for a in p1.iter() {
        for b in p2.iter() {
            res.push(a.iter()
                .chain(b.iter().skip(1))
                .cloned()
                .collect::<Vec<_>>());
        }
    }
    res
}

/// Computes all shortests paths between every pair of edges.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::shortests_paths;
/// let mut g = GraphNauty::new(0);
/// for _ in 0..11
/// {
///     g.add_vertex();
/// }
/// for i in 0..10
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(10,0);
/// shortests_paths(&g);
/// ```
pub fn shortests_paths<'a, G>(g: &'a G) -> Vec<Vec<Vec<Vec<u64>>>>
    where G: GraphIter<'a>
{
    let n = g.order() as usize;
    let mut paths = vec![vec![vec![]; n]; n];
    for u in g.vertices().map(|x| x as usize) {
        paths[u][u].push(vec![u as u64]);
    }
    let mut verts = g.vertices();
    while let Some(u) = verts.next() {
        let mut verts2 = verts.clone();
        while let Some(v) = verts2.next() {
            if g.is_edge(u,v) {
                paths[u as usize][v as usize].push(vec![u, v]);
                paths[v as usize][u as usize].push(vec![v, u]);
            }
        }
    }
    for k in g.vertices().map(|x| x as usize) {
        for u in g.vertices().map(|x| x as usize).filter(|&x| x != k) {
            for v in g.vertices()
                .map(|x| x as usize)
                .filter(|&x| x != k && x != u) {
                let duk = shortests_paths_length(&paths[u][k]);
                let dkv = shortests_paths_length(&paths[k][v]);
                let duv = shortests_paths_length(&paths[u][v]);
                let dukv = duk.saturating_add(dkv);
                if duv >= dukv {
                    if duv > dukv {
                        paths[u][v].clear();
                    }
                    let mut new_paths = combine_paths(&paths[u][k], &paths[k][v]);
                    paths[u][v].append(&mut new_paths);
                }
            }
        }
    }
    paths
}

/// Computes the average eccentricity of the graph.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::avecc;
/// let mut g = GraphNauty::new(5);
/// for i in 0..5 {
///     g.add_edge(i,(i+1)%5);
/// }
/// assert!((avecc(&g) - 2f64).abs() < 1e-10);
/// ```
pub fn avecc<'a, G>(g: &'a G) -> f64
    where G: GraphIter<'a>
{
    if g.order() == 0 {
        0f64
    } else {
        let dm = floyd_warshall(g);
        let t: Distance = dm.iter()
            .map(|x| x.iter().max().unwrap_or(&Distance::Val(0)))
            .fold(Distance::Val(0), |acc, &x| acc + x);
        match t {
            Distance::Val(x) => x as f64 / g.order() as f64,
            Distance::Inf => f64::INFINITY,
        }
    }
}

/// Computes the average distance of the graph.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::avdist;
/// let mut g = GraphNauty::new(5);
/// for i in 0..5 {
///     g.add_edge(i,(i+1)%5);
/// }
/// assert!((avdist(&g) - 1.5).abs() < 1e-10);
/// ```
pub fn avdist<'a, G>(g: &'a G) -> f64
    where G: GraphIter<'a>
{
    if g.order() == 0 {
        0f64
    } else {
        let dm = floyd_warshall(g);
        let s: Distance = dm.iter()
            .flat_map(|x| x.iter())
            .fold(Distance::Val(0), |acc, &x| acc + x);
        let n = g.order();
        match s {
            Distance::Val(x) => x as f64 / (n * (n - 1)) as f64,
            Distance::Inf => f64::INFINITY,
        }
    }
}

/// Computes the difference between the average eccentricity and the average distance.
/// This does not reuse avecc and avdist to avoid computing the distance matrix two times instead
/// of one.
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::minus_avecc_avdist;
/// let mut g = GraphNauty::new(5);
/// for i in 0..3
/// {
///     g.add_edge(i+1,i);
///     g.add_edge(4,i);
/// }
/// assert!((minus_avecc_avdist(&g) - 18.0/20.0).abs() < 1e-10);
/// g.remove_edge(4,2);
/// assert!((minus_avecc_avdist(&g) - 18.0/20.0).abs() < 1e-10);
/// ```
pub fn minus_avecc_avdist<'a, G>(g: &'a G) -> f64
    where G: GraphIter<'a>
{
    let dm = floyd_warshall(g);
    let default_max = Distance::Val(0);
    let n: f64 = g.order() as f64;
    let sum: f64 = match dm.iter()
        .flat_map(|x| x.iter())
        .fold(Distance::Val(0), |acc, &x| acc + x) {
        Distance::Val(v) => v as f64,
        _ => f64::INFINITY,
    };
    let sum_ecc: f64 = match dm.iter()
        .map(|x| x.iter().max().unwrap_or(&default_max))
        .fold(Distance::Val(0), |acc, &x| acc + x) {
        Distance::Val(v) => v as f64,
        _ => f64::INFINITY,
    };
    if sum_ecc < f64::INFINITY {
        ((n - 1f64) * sum_ecc - sum) / (n * (n - 1f64))
    } else {
        f64::INFINITY
    }
}

/// Computes the eccentric connectivity index of a graph
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::eci;
/// let mut g = GraphNauty::new(5);
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(4,0);
/// assert!(eci(&g).unwrap() == 20);
/// let mut g = GraphNauty::new(6);
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(2,5);
/// g.add_edge(3,5);
/// assert!(eci(&g).unwrap() == 35);
/// ```
pub fn eci<'a, G>(g: &'a G) -> Result<u64, DisconnectedGraph>
    where G: GraphIter<'a>
{
    let dm = floyd_warshall(g);
    let eccs: Vec<Distance> = dm.iter().map(|x| (*x.iter().max().unwrap())).collect();
    let degrees: Vec<u64> = g.vertices()
        .map(|x| g.neighbors(x).count() as u64)
        .collect();
    eccs.iter()
        .zip(degrees.iter())
        .map(|(a, b)| match *a {
            Distance::Val(v) => Ok(v * *b),
            _ => Err(DisconnectedGraph::new("eci")),
        })
        .fold(Ok(0), |acc, x: Result<u64, DisconnectedGraph>| {
            match (acc, x) {
                (Ok(v), Ok(o)) => Ok(v + o),
                _ => Err(DisconnectedGraph::new("eci")),
            }
        })
}

/// Computes the number of dominant vertices
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::num_dom;
/// let mut g = GraphNauty::new(5);
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(4,0);
/// assert!(num_dom(&g) == 0);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(num_dom(&g) == 1);
/// for i in 2..5
/// {
///     g.add_edge(1,i);
/// }
/// assert!(num_dom(&g) == 3);
/// ```
pub fn num_dom<'a, G>(g: &G) -> u64
    where G: GraphIter<'a>
{
    let n = g.order();
    g.vertices()
        .map(|x| g.neighbors(x).count() as u64)
        .filter(|&x| x == n - 1)
        .count() as u64
}

/// Computes the number of pending vertices
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::num_pending;
/// let mut g = GraphNauty::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(num_pending(&g) == 4);
/// g.add_edge(2,1);
/// assert!(num_pending(&g) == 2);
/// g.add_edge(3,1);
/// assert!(num_pending(&g) == 1);
/// g.add_edge(4,1);
/// assert!(num_pending(&g) == 0);
/// ```
pub fn num_pending<'a, G>(g: &G) -> u64
    where G: GraphIter<'a>
{
    g.vertices()
        .map(|x| g.neighbors(x).count() as u64)
        .filter(|&x| x == 1)
        .count() as u64
}

/// Diameter of Hnm with same order and size as the graph
/// given in parameter. Hnm is the graph on n vertices and m edges obtained by taking the biggest
/// clique that does not disconnect the graph and adding a path with the remaining vertices linked
/// to a vertex of the clique. If there are remaining edges, they are added between the closest
/// vertex of the path to the clique and vertices of the clique.
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::dnm;
/// let mut g = GraphNauty::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// dnm(&g);
/// ```
pub fn dnm<G>(g: &G) -> u64
    where G: Graph
{
    let n = g.order() as f64;
    let m = g.size() as f64;
    ((2f64 * n + 1f64 - (17f64 + 8f64 * (m - n)).sqrt()) / 2f64).floor() as u64
}

/// Computes the maximum degree in the graph.
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::deg_max;
/// let mut g = GraphNauty::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(deg_max(&g) == 4);
/// ```
pub fn deg_max<'a, G>(g: &G) -> u64
    where G: GraphIter<'a>
{
    g.vertices()
        .map(|x| g.neighbors(x).count() as u64)
        .max()
        .unwrap()
}

/// Computes the minimum degree in the graph.
///
/// # Examples
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty};
/// use graph::invariants::deg_min;
/// let mut g = GraphNauty::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(deg_min(&g) == 1);
/// ```
pub fn deg_min<'a, G>(g: &G) -> u64
    where G: GraphIter<'a>
{
    g.vertices()
        .map(|x| g.neighbors(x).count() as u64)
        .min()
        .unwrap()
}

/// Computes the irregularity of a graph. This invariant is defined as the sum for all edges of the
/// absolute value of the difference between the degrees of its extremities.
/// If the graph has no edges, 0 is returned.
///
/// # Examples
/// ```
/// use graph::{Graph,GraphNauty};
/// use graph::invariants::irregularity;
/// use graph::format::from_g6;
///
/// let mut g: GraphNauty = from_g6(&"C^".to_string()).unwrap();
/// assert!(irregularity(&g) == 4);
///
/// g = from_g6(&"DDW".to_string()).unwrap();
/// assert!(irregularity(&g) == 2);
///
/// g = from_g6(&"D??".to_string()).unwrap();
/// assert!(irregularity(&g) == 0);
/// ```
pub fn irregularity<'a, G>(g: &'a G) -> u64
    where G: GraphIter<'a>
{
    let degrees = g.vertices()
        .map(|x| g.neighbors(x).count() as isize)
        .collect::<Vec<isize>>();
    let mut sum = 0;
    let mut verts = g.vertices();
    while let Some(x) = verts.next() {
        let mut verts2 = verts.clone();
        while let Some(y) = verts2.next() {
            if g.is_edge(x,y) {
                sum += (degrees[x as usize] - degrees[y as usize]).abs() as u64
            }
        }
    }
    sum
}

// TODO: documentation and test
pub fn avg_clique_size<'a, G>(g: &'a G) -> f64
    where G: Graph + GraphIter<'a> {
    let (nb_cliques, total_cliques_size) = cliques(g).fold(
        (0, 0),
        |(nb_cliques, total_cliques_size), clique|
            (nb_cliques + 1, total_cliques_size + clique.len() as u64)
    );
    return (total_cliques_size as f64) / (nb_cliques as f64);
}

// TODO: documentation and test
pub fn avg_indep_size<'a, G>(g: &'a G) -> f64
    where G: Graph + GraphIter<'a> {
    let n = g.order();
    let (nb_cliques, total_cliques_size) = cliques(g).fold(
        (0, 0),
        |(nb_cliques, total_cliques_size), clique|
            (nb_cliques + 1, total_cliques_size + (n - clique.len() as u64))
    );
    return (total_cliques_size as f64) / (nb_cliques as f64);
}