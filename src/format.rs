//! Module containing functions to handle different graph formats such as graph6

use Graph;
use errors::*;

/// Returns the length of the graph6 format for a graph of order n
fn length_g6(n: u64) -> u64 {
    if n > 0 {
        1 + (((n * (n - 1)) / 2) as f64 / 6f64).ceil() as u64
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
/// g.add_vertex();
/// assert!("@" == format::to_g6(&g));
/// g.add_vertex();
/// assert!("A?" == format::to_g6(&g));
/// g.add_edge(0,1);
/// assert!("A_" == format::to_g6(&g));
/// for _ in 0..9
/// {
///     g.add_vertex();
/// }
/// for u in g.vertices().skip(1)
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
        for u in graph.vertices().skip(1) {
            for v in graph.vertices().take_while(|x| *x != u) {
                if l == 6 {
                    res += &((r + 63) as char).to_string();
                    l = 0;
                    r = 0;
                }
                r <<= 1;
                if graph.is_edge(u, v) {
                    r += 1;
                }
                l += 1;
            }
        }
        if l <= 6 {
            r <<= 6 - l;
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
pub fn from_g6(s: &str) -> Result<Graph, InvalidGraph6> {
    let mut chars = s.chars();
    if let Some(n) = chars.next().and_then(|x| Some(u64::from((x as u8) - 63))) {
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

/// Convert a set of big endians 64 bits numbers into a string using graph6 chars
///
/// # Examples:
/// ```
/// use graph::format::encode;
/// //abc in binary
/// let mut res = encode(&[0x1e5b7be000000000],5);
/// let mut expected = "Fdlzw";
/// assert_eq!(res,expected);
/// res = encode(&[0x1e5b7be000000000],3);
/// expected = "Fdl";
/// assert_eq!(res,expected);
/// res = encode(&[0x3800000c004043d8,0xfffeffef00000000],17);
/// expected = "M???B?@?O|b~~n~n?";
/// assert_eq!(res,expected);
/// ```
pub fn encode(data: &[u64], l: u64) -> String {
    let mut res = String::with_capacity(l as usize);
    if data.len() > 0 {
        let mut l = l;
        let mut pdata = 1;
        let mut p = 0;
        let mut v = data[0].to_be_bytes();
        let mut r: u64 = 0;
        let mut n = 0;
        while l > 0 {
            // We take 3 bytes or as many as available
            while n < 3 && p < 8 {
                r += (v[p] as u64) << (8 * (2 - n));
                p += 1;
                n += 1;
            }
            // If not enough bytes left in current number, we take the next one if there is one.
            if n < 3 && pdata < data.len() {
                p = 0;
                v = data[pdata].to_be_bytes();
                pdata += 1;
            } else {
                //When we have 24 bytes, we convert them into 4 chars or less if not enough data
                // Reverse order of 6 bits sets
                let x = ((r >> 18) ^ r) & 63;
                let y = ((r >> 12) ^ (r >> 6)) & 63;
                r = r ^ ((x << 18) | (y << 12) | (y << 6) | x);
                for _ in 0..4.min(l) {
                    res.push(((r & 63) as u8 + 63) as char);
                    r /= 64;
                    l -= 1;
                }
                n = 0;
                r = 0;
            }
        }
    }
    res
}

/// Convert string using graph6 chars into a set of big endians 64 bits numbers.
///
/// # Examples:
/// ```
/// use graph::format::decode;
/// let mut res = decode("Fdlzw");
/// let mut expected = vec![0x1e5b7be000000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// res = decode("Fdl");
/// expected = vec![0x1e5b400000000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// res = decode("M???B?@?O|b~~n~n?");
/// expected = vec![0x3800000c004043d8,0xfffeffef00000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// ```
pub fn decode(data: &str) -> Vec<u64> {
    dbg!(data);
    let capa = (((data.len() * 6) as f64) / 64.).ceil() as usize;
    let mut res = Vec::with_capacity(capa);
    if data.len() > 0 {
        let data = data.as_bytes();
        let mut cur = [0u8; 8];
        let mut pdata = 0;
        let mut p = 0;
        let mut v: u64 = 0;
        while pdata < data.len() {
            // We take 4 chars or as many available
            for _ in 0..4 {
                v = v << 6;
                if pdata < data.len() {
                    v += (data[pdata] as u64) - 63;
                    pdata += 1;
                }
            }
            // We convert these 24 bits into 3 bytes
            for i in 0..3 {
                if p == 8 && res.len() < capa {
                    res.push(u64::from_be_bytes(cur));
                    cur = [0u8; 8];
                    p = 0;
                }
                if p < 8 {
                    cur[p] = ((v >> (8 * (2 - i))) & 255) as u8;
                    p += 1;
                }
            }
        }
        if p > 0 {
            res.push(u64::from_be_bytes(cur));
        }
    }
    res
}

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
