//! Implementations of different graph invariants

use super::Graph;
use std::usize::MAX;
use std::f64;
use errors::*;
use std::collections::VecDeque;

///
/// Represents distances that can be infinite.
/// # Examples
///
/// ```
/// use graph::Graph;
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
#[derive(Clone, Copy, Debug)]
pub enum Distance {
    /// Infinite distance
    Inf,
    /// Finite distance
    Val(usize),
}

impl Distance {
    /// Returns the value of a finite distance and None if the distance was infinite.
    ///
    /// # Examples
    /// ```
    /// use graph::invariants::Distance;
    /// assert!(Distance::Val(6).get_val().is_some());
    /// ```
    pub fn get_val(&self) -> Option<usize> {
        match *self {
            Distance::Inf => None,
            Distance::Val(x) => Some(x),
        }
    }

    /// Returns true if the value is finite and false otherwise.
    pub fn is_finite(&self) -> bool {
        match *self {
            Distance::Val(_) => true,
            Distance::Inf => false,
        }
    }
}

impl ::std::fmt::Display for Distance {
    fn fmt(&self, f: &mut ::fmt::Formatter) -> ::fmt::Result {
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
/// usize::MAX is used to represent infinity since the graph representation cannot have more than 11
/// vertices.
///
/// # Examples
///
/// ```
/// use std::usize::MAX;
/// use graph::Graph;
/// use graph::invariants::floyd_warshall;
/// use graph::invariants::Distance::{Val,Inf};
///
/// fn to_usize(v: Vec<Vec<graph::invariants::Distance>>) -> Vec<Vec<usize>>
/// {
///     v.iter().map(|x| x.iter().map(|x| match x {&Val(v) => v, &Inf => MAX}).collect()).collect()
/// }
///
/// let mut g = Graph::new(0);
/// let distances: Vec<Vec<usize>> = to_usize(floyd_warshall(&g));
/// assert!(distances.len() == 0);
/// g.add_vertex();
/// let distances: Vec<Vec<usize>> = to_usize(floyd_warshall(&g));
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
/// let distances: Vec<Vec<usize>> = to_usize(floyd_warshall(&g));
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
/// for u in g.vertices()
/// {
///     for v in g.vertices()
///     {
///         println!("{}, {}",u,v);
///         println!("{}, {}",distances[u][v],expected_distances[u][v]);
///         assert!(distances[u][v] == expected_distances[u][v]);
///     }
/// }
/// ```
pub fn floyd_warshall(g: &Graph) -> Vec<Vec<Distance>> {
    use self::Distance::{Inf, Val};
    let n = g.order();
    let mut matrix = vec![vec![Inf; n]; n];
    for u in g.vertices() {
        matrix[u][u] = Val(0);
    }
    for (u, v) in g.edges() {
        matrix[u][v] = Val(1);
        matrix[v][u] = Val(1);
    }
    for k in g.vertices() {
        for u in g.vertices() {
            for v in g.vertices() {
                if matrix[u][v] > matrix[u][k] + matrix[k][v] {
                    matrix[u][v] = matrix[u][k] + matrix[k][v];
                }
            }
        }
    }
    matrix
}

pub fn diameter(g: &Graph) -> Distance {
    if g.order() > 0 {
        let distances = floyd_warshall(&g);
        *distances.iter()
            .map(|x| x.iter().max().unwrap())
            .max()
            .unwrap()
    } else {
        Distance::Inf
    }
}

fn dfs(g: &Graph, u: usize, visited: &mut Vec<bool>) -> Vec<usize> {
    let mut comp = vec![];
    let mut to_visit = vec![u];
    while !to_visit.is_empty() {
        let v = to_visit.pop().unwrap();
        if !visited[v] {
            comp.push(v);
            for w in g.neighbors(v) {
                to_visit.push(w);
            }
            visited[v] = true;
        }
    }
    comp
}

/// Returns all the shortests paths from start
///
///  # Examples
///
///  ```
///  use graph::Graph;
///  use graph::invariants::{bfs, Distance};
///  use graph::format::from_g6;
///
///  let g = from_g6(&String::from("GiGoG?")).unwrap();
///  let res = bfs(&g,0);
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
pub fn bfs(g: &Graph, start: usize) -> (Vec<Distance>, Vec<Vec<usize>>) {
    let mut dists: Vec<Distance> = [Distance::Inf]
        .iter()
        .cycle()
        .take(g.order())
        .cloned()
        .collect();
    let mut paths: Vec<Vec<usize>> = [Vec::new()]
        .iter()
        .cycle()
        .take(g.order())
        .cloned()
        .collect();
    dists[start] = Distance::Val(0);
    let mut frontier = VecDeque::with_capacity(1);
    frontier.push_back(start);
    while !frontier.is_empty() {
        let cur = frontier.pop_front().unwrap();
        let cdist = dists[cur] + Distance::Val(1);
        for n in g.neighbors(cur) {
            let ndist = dists[n];
            // ndist was infinite (we know it because it is a bfs)
            if ndist > cdist {
                dists[n] = cdist;
                paths[n].clear();
                paths[n].push(cur);
                frontier.push_back(n);
                // there is another shortest path to join n
            } else if ndist == cdist {
                paths[n].push(cur);
            }
        }
    }
    (dists, paths)
}

/// Computes the eccentricities of the graph
///
/// # Examples
///
/// ```
/// use graph::Graph;
/// use graph::invariants::{eccentricities, Distance};
/// use graph::format::from_g6;
///
/// let g = from_g6(&String::from("FiGoG")).unwrap();
/// let expected:Vec<Distance> = [4,3,2,3,3,3,4].iter().map(|&x| Distance::Val(x)).collect();
/// let r = eccentricities(&g);
/// assert_eq!(r.len(), expected.len());
/// for (i,e) in r.iter().enumerate() {
///     assert_eq!(*e,expected[i]);
/// }
/// ```
pub fn eccentricities(g: &Graph) -> Vec<Distance> {
    floyd_warshall(&g)
        .iter()
        .map(|x| *x.iter().max().unwrap())
        .collect()
}

fn construct_paths(pths: &[Vec<usize>], s: usize, e: usize) -> Vec<Vec<usize>> {
    let mut res = vec![];
    if pths[e].is_empty() || s == e {
        res.push(vec![e]);
        res
    } else {
        for &t in &pths[e] {
            let mut tres = construct_paths(pths, s, t);
            for mut p in tres {
                p.push(e);
                res.push(p);
            }
        }
        res
    }
}

///
///
/// # Examples
///
/// ```
/// use graph::Graph;
/// use graph::invariants::{diametral_paths, Distance};
/// use graph::format::from_g6;
///
/// let g = from_g6(&String::from("FiGoG")).unwrap();
/// let r = diametral_paths(&g);
/// println!("{:?}",r);
/// panic!();
/// ```
pub fn diametral_paths(g: &Graph) -> Vec<Vec<usize>> {
    let eccs = eccentricities(&g);
    let diam = eccs.iter().max().unwrap();
    let extms: Vec<usize> = (0..g.order()).filter(|&x| eccs[x] == *diam).collect();
    let mut res = vec![];
    // println!("{:?}", extms);
    for e in extms {
        let (dsts, pths) = bfs(&g, e);
        for (i, _dst) in dsts.iter().enumerate().filter(|&(_x, y)| y == diam) {
            let mut tres = construct_paths(&pths, e, i);
            res.append(&mut tres);
        }
    }
    res
}

/// Returns the connected components of the graph.
///
/// # Examples
///
/// ```
/// use graph::Graph;
/// use graph::invariants::connected_components;
/// let mut g = Graph::new(0);
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
pub fn connected_components(g: &Graph) -> Vec<Vec<usize>> {
    let mut comps = vec![];
    let mut visited = vec![false; g.order()];
    for u in g.vertices() {
        if !visited[u] {
            comps.push(dfs(&g, u, &mut visited));
        }
    }
    comps
}

pub fn is_connected(g: &Graph) -> bool {
    connected_components(g).len() < 2
}

fn shortests_paths_length(p: &[Vec<usize>]) -> usize {
    if !p.is_empty() { p[0].len() - 1 } else { MAX }
}

fn combine_paths(p1: &[Vec<usize>], p2: &[Vec<usize>]) -> Vec<Vec<usize>> {
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
/// use graph::Graph;
/// use graph::invariants::shortests_paths;
/// let mut g = Graph::new(0);
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
pub fn shortests_paths(g: &Graph) -> Vec<Vec<Vec<Vec<usize>>>> {
    let n = g.order();
    let mut paths = vec![vec![vec![]; n]; n];
    for u in g.vertices() {
        paths[u][u].push(vec![u]);
    }
    for (u, v) in g.edges() {
        paths[u][v].push(vec![u, v]);
        paths[v][u].push(vec![v, u]);
    }
    for k in g.vertices() {
        for u in g.vertices().filter(|&x| x != k) {
            for v in g.vertices().filter(|&x| x != k && x != u) {
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
/// use graph::Graph;
/// use graph::invariants::avecc;
/// let mut g = Graph::new(5);
/// for i in 0..5 {
///     g.add_edge(i,(i+1)%5);
/// }
/// assert!((avecc(&g) - 2f64).abs() < 1e-10);
/// ```
pub fn avecc(g: &Graph) -> f64 {
    if g.order() == 0 {
        0f64
    } else {
        let dm = floyd_warshall(&g);
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
/// use graph::Graph;
/// use graph::invariants::avdist;
/// let mut g = Graph::new(5);
/// for i in 0..5 {
///     g.add_edge(i,(i+1)%5);
/// }
/// assert!((avdist(&g) - 1.5).abs() < 1e-10);
/// ```
pub fn avdist(g: &Graph) -> f64 {
    if g.order() == 0 {
        0f64
    } else {
        let dm = floyd_warshall(&g);
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
/// use graph::Graph;
/// use graph::invariants::minus_avecc_avdist;
/// let mut g = Graph::new(5);
/// for i in 0..3
/// {
///     g.add_edge(i+1,i);
///     g.add_edge(4,i);
/// }
/// assert!((minus_avecc_avdist(&g) - 18.0/20.0).abs() < 1e-10);
/// g.remove_edge(4,2);
/// assert!((minus_avecc_avdist(&g) - 18.0/20.0).abs() < 1e-10);
/// ```
pub fn minus_avecc_avdist(g: &Graph) -> f64 {
    let dm = floyd_warshall(&g);
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
/// use graph::Graph;
/// use graph::invariants::eci;
/// let mut g = Graph::new(5);
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(4,0);
/// assert!(eci(&g).unwrap() == 20);
/// let mut g = Graph::new(6);
/// for i in 0..4
/// {
///     g.add_edge(i,i+1);
/// }
/// g.add_edge(2,5);
/// g.add_edge(3,5);
/// assert!(eci(&g).unwrap() == 35);
/// ```
pub fn eci(g: &Graph) -> Result<usize, DisconnectedGraph> {
    let dm = floyd_warshall(&g);
    let eccs: Vec<Distance> = dm.iter().map(|x| (*x.iter().max().unwrap())).collect();
    let degrees: Vec<usize> = g.vertices()
        .map(|x| g.neighbors(x).count())
        .collect();
    eccs.iter()
        .zip(degrees.iter())
        .map(|(a, b)| match *a {
            Distance::Val(v) => Ok(v * *b),
            _ => Err(DisconnectedGraph::new("eci")),
        })
        .fold(Ok(0), |acc, x: Result<usize, DisconnectedGraph>| {
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
/// use graph::Graph;
/// use graph::invariants::num_dom;
/// let mut g = Graph::new(5);
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
pub fn num_dom(g: &Graph) -> usize {
    let n = g.order();
    g.vertices()
        .map(|x| g.neighbors(x).count())
        .filter(|&x| x == n - 1)
        .count()
}

/// Computes the number of pendant vertices
///
/// # Examples
/// ```
/// use graph::Graph;
/// use graph::invariants::num_pendant;
/// let mut g = Graph::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(num_pendant(&g) == 4);
/// g.add_edge(2,1);
/// assert!(num_pendant(&g) == 2);
/// g.add_edge(3,1);
/// assert!(num_pendant(&g) == 1);
/// g.add_edge(4,1);
/// assert!(num_pendant(&g) == 0);
/// ```
pub fn num_pendant(g: &Graph) -> usize {
    g.vertices()
        .map(|x| g.neighbors(x).count())
        .filter(|&x| x == 1)
        .count()
}

/// # Examples
/// ```
/// use graph::Graph;
/// use graph::invariants::dnm;
/// let mut g = Graph::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// dnm(&g);
/// ```
pub fn dnm(g: &Graph) -> usize {
    let n = g.order() as f64;
    let m = g.size() as f64;
    ((2f64 * n + 1f64 - (17f64 + 8f64 * (m - n)).sqrt()) / 2f64).floor() as usize
}

/// # Examples
/// ```
/// use graph::Graph;
/// use graph::invariants::deg_max;
/// let mut g = Graph::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// println!("{}",deg_max(&g));
/// assert!(deg_max(&g) == 4);
/// ```
pub fn deg_max(g: &Graph) -> usize {
    g.vertices()
        .map(|x| g.neighbors(x).count())
        .max()
        .unwrap()
}

/// # Examples
/// ```
/// use graph::Graph;
/// use graph::invariants::deg_min;
/// let mut g = Graph::new(5);
/// for i in 1..5
/// {
///     g.add_edge(0,i);
/// }
/// assert!(deg_min(&g) == 1);
/// ```
pub fn deg_min(g: &Graph) -> usize {
    g.vertices()
        .map(|x| g.neighbors(x).count())
        .min()
        .unwrap()
}

/// Computes the irregularity of a graph. This invariant is defined as the sum for all edges of the
/// absolute value of the difference between the degrees of its extremities.
/// If the graph has no edges, 0 is returned.
///
/// # Examples
/// ```
/// use graph::Graph;
/// use graph::invariants::irregularity;
/// use graph::format::from_g6;
///
/// let mut g = from_g6(&"C^".to_string()).unwrap();
/// assert!(irregularity(&g) == 4);
///
/// g = from_g6(&"DDW".to_string()).unwrap();
/// assert!(irregularity(&g) == 2);
///
/// g = from_g6(&"D??".to_string()).unwrap();
/// assert!(irregularity(&g) == 0);
/// ```
pub fn irregularity(g: &Graph) -> usize {
    let degrees = g.vertices()
        .map(|x| g.neighbors(x).count() as isize)
        .collect::<Vec<isize>>();
    g.edges()
        .map(|(x, y)| (degrees[x] - degrees[y]).abs() as usize)
        .sum()
}