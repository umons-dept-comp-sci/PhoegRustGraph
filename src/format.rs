//! Module containing functions to handle different graph formats such as graph6

use Graph;
use errors::*;

/// Returns the length of the graph6 format for a graph of order n
fn length_g6(n: usize) -> usize {
    if n > 0 {
        1 + (((n * (n - 1)) / 2) as f64 / 6f64).ceil() as usize
    } else {
        1
    }
}

/// Returns the graph6 representation of a graph
///
/// # Examples
///
/// ```
/// use graph::Graph;
/// use graph::format;
/// let mut g = Graph::new(0);
/// assert!("?" == format::to_g6(&g));
/// g.add_node();
/// assert!("@" == format::to_g6(&g));
/// g.add_node();
/// assert!("A?" == format::to_g6(&g));
/// g.add_edge(0,1);
/// assert!("A_" == format::to_g6(&g));
/// for _ in 0..9
/// {
///     g.add_node();
/// }
/// for u in g.nodes_iter().skip(1)
/// {
///     g.add_edge(u,u-1);
/// }
/// assert!("JhCGGC@?G?_" == format::to_g6(&g));
/// ```
pub fn to_g6(graph: &Graph) -> String {
    let n = graph.order();
    let mut res = String::new();
    res += &((n as u8 + 63) as char).to_string();
    if graph.size() == 0 {
        for _ in 1..length_g6(n) {
            res += &'?'.to_string();
        }
    } else {
        let mut l = 0;
        let mut r: u8 = 0;
        for u in graph.nodes_iter().skip(1) {
            for v in graph.nodes_iter().take_while(|x| *x != u) {
                if l == 6 {
                    res += &((r + 63) as char).to_string();
                    l = 0;
                    r = 0;
                }
                r = r << 1;
                if graph.is_edge(u, v) {
                    r += 1;
                }
                l += 1;
            }
        }
        if l <= 6 {
            r = r << (6 - l);
            res += &((r + 63) as char).to_string();
        }
    }
    res
}

/// Returns a graph corresponding to the graph6 representation
///
/// # Examples
///
/// ```
/// use graph::format;
/// use graph::errors::*;
/// let mut g;
/// g = format::from_g6(&"?".to_string()).unwrap();
/// assert!(g.order() == 0);
/// g = format::from_g6(&"@".to_string()).unwrap();
/// assert!(g.order() == 1);
/// g = format::from_g6(&"A?".to_string()).unwrap();
/// assert!(g.order() == 2);
/// assert!(!g.is_edge(0,1));
/// g = format::from_g6(&"A_".to_string()).unwrap();
/// assert!(g.order() == 2);
/// assert!(g.is_edge(0,1));
/// g = format::from_g6(&"JhCGGC@?G?_".to_string()).unwrap();
/// assert!(g.order() == 11);
/// for u in 0..11
/// {
///     for v in 0..u
///     {
///         println!("{} {}",u,v);
///         if u-v == 1
///         {
///             assert!(g.is_edge(u,v));
///         }
///         else
///         {
///             assert!(!g.is_edge(u,v));
///         }
///     }
/// }
/// match format::from_g6(&"Z".to_string()) {
///     Err(InvalidGraph6) => (),
///     _ => assert!(false),
/// }
/// ```
pub fn from_g6(s: &String) -> Result<Graph, InvalidGraph6> {
    let mut chars = s.chars();
    if let Some(n) = chars.next().and_then(|x| Some(((x as u8) - 63) as usize)) {
        let mut g = Graph::new(n);
        if n > 1 && s.len() == 1 + (((n * (n - 1)) as f64 / 12.0).ceil() as usize) {
            let mut l = 6;
            if let Some(mut v) = chars.next().and_then(|x| Some(x as u8 - 63)) {
                for i in 1..n {
                    for j in 0..i {
                        if l == 0 {
                            l = 6;
                            v = match chars.next().and_then(|x| Some(x as u8 - 63)) {
                                Some(x) => x,
                                None => return Err(InvalidGraph6::new(s)),
                            };
                        }
                        if (v % (1 << l)) >> (l - 1) > 0 {
                            g.add_edge(i, j);
                        }
                        l -= 1;
                    }
                }
                Ok(g)
            } else {
                Err(InvalidGraph6::new(s))
            }
        } else if n > 1 && s.len() != 1 + (((n * (n - 1)) as f64 / 12.0).floor() as usize) {
            Err(InvalidGraph6::new(s))
        } else {
            Ok(g)
        }
    } else {
        Err(InvalidGraph6::new(s))
    }
}

// Returns a graph corresponding to the graph6 representation
//
// # Examples
//
// ```
// use graph::Graph;
// use graph::format;
// let mut g;
// g = format::from_g6(&"?".to_string()).unwrap();
// assert!(g.order() == 0);
// g = format::from_g6(&"@".to_string()).unwrap();
// assert!(g.order() == 1);
// g = format::from_g6(&"A?".to_string()).unwrap();
// assert!(g.order() == 2);
// assert!(!g.is_edge(0,1));
// g = format::from_g6(&"A_".to_string()).unwrap();
// assert!(g.order() == 2);
// assert!(g.is_edge(0,1));
// g = format::from_g6(&"JhCGGC@?G?_".to_string()).unwrap();
// assert!(g.order() == 11);
// for u in 0..11
// {
//     for v in 0..u
//     {
//         println!("{} {}",u,v);
//         if u-v == 1
//         {
//             assert!(g.is_edge(u,v));
//         }
//         else
//         {
//             assert!(!g.is_edge(u,v));
//         }
//     }
// }
// ```
// pub fn from_g6(s: &String) -> ::std::result::Result<Graph, &str> {
// let mut chars = s.chars();
// if let Some(n) = chars.next().and_then(|x| Some(((x as u8) - 63) as usize)) {
// let mut g = Graph::new(n);
// if n > 1 && s.len() == 1 + (((n * (n - 1)) as f64 / 12.0).ceil() as usize) {
// let mut l = 6;
// let mut v = chars.next().expect("Invalid graph6 format : too short") as u8 - 63;
// for i in 1..n {
// for j in 0..i {
// if l == 0 {
// l = 6;
// v = chars.next().expect("Invalid graph6 format : too short") as u8 - 63;
//
// if (v % (1 << l)) >> (l - 1) > 0 {
// g.add_edge(i, j);
//
// l -= 1;
//
//
// Ok(g)
// else if n > 1 && s.len() != 1 + (((n * (n - 1)) as f64 / 12.0).floor() as usize) {
// Err(s)
// else {
// Ok(g)
//
// else {
// Err(s)
//
//

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn length_g6_test() {
        assert!(length_g6(0) == 1);
        assert!(length_g6(1) == 1);
        assert!(length_g6(2) == 2);
        assert!(length_g6(10) == 9);
    }
}
