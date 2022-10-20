//! Module containing functions to handle different graph formats such as graph6

use crate::errors::*;
use crate::GraphFormat;

#[allow(dead_code)]
/// Returns the length of the order of a graph in graph6 format
fn length_order_g6(n: u64) -> u64 {
    if n <= 62 {
        1
    } else if n <= 258047 {
        4
    } else {
        8
    }
}

#[allow(dead_code)]
/// Returns the length of the graph6 format for a graph of order n
fn length_g6(n: u64) -> u64 {
    if n > 0 {
        length_order_g6(n) + (((n * (n - 1)) / 2) as f64 / 6f64).ceil() as u64
    } else {
        1
    }
}

/// Returns the graph6 representation of a graph
///
/// # Examples
///
/// ```
/// use graph::{Graph,GraphConstructible,GraphNauty,GraphIter};
/// use graph::format;
/// let mut g = GraphNauty::new(0);
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
pub fn to_g6<G>(graph: &G) -> String
where
    G: GraphFormat,
{
    let n = graph.order();
    let m = if n > 0 {
        ((n * (n - 1) / 2) as f64 / 6.).ceil() as u64
    } else {
        0
    };
    encode(&graph.to_bin(), length_order_g6(n) + m)
}

/// Returns a graph corresponding to the graph6 representation
///
/// # Examples
///
/// ```
/// use graph::Graph;
/// use graph::GraphNauty;
/// use graph::format;
/// use graph::errors::*;
/// let mut g: GraphNauty;
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
/// match format::from_g6::<GraphNauty>(&"Z".to_string()) {
///     Err(InvalidGraph6) => (),
///     _ => assert!(false),
/// }
/// ```
pub fn from_g6<G>(s: &str) -> Result<G, InvalidGraph6>
where
    G: GraphFormat,
{
    let bin = decode(s)?;
    G::from_bin(&bin).map_err(|x| x.into())
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
    if !data.is_empty() {
        let mut l = l;
        let mut pdata = 1;
        let mut p = 0;
        let mut v = data[0].to_be_bytes();
        let mut r: u64 = 0;
        let mut n = 0;
        while l > 0 {
            // We take 3 bytes or as many as available
            while n < 3 && p < 8 {
                r += (u64::from(v[p])) << (8 * (2 - n));
                p += 1;
                n += 1;
            }
            // If not enough bytes left in current number, we take the next one if there is one.
            if n < 3 && pdata < data.len() {
                p = 0;
                v = data[pdata].to_be_bytes();
                pdata += 1;
            } else {
                // When we have 24 bytes, we convert them into 4 chars or less if not enough data
                // Reverse order of 6 bits sets
                let x = ((r >> 18) ^ r) & 63;
                let y = ((r >> 12) ^ (r >> 6)) & 63;
                r ^= (x << 18) | (y << 12) | (y << 6) | x;
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
/// let mut res = decode("Fdlzw").unwrap();
/// let mut expected = vec![0x1e5b7be000000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// res = decode("Fdl").unwrap();
/// expected = vec![0x1e5b400000000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// res = decode("M???B?@?O|b~~n~n?").unwrap();
/// expected = vec![0x3800000c004043d8,0xfffeffef00000000];
/// assert_eq!(res.len(),expected.len());
/// for (r,e) in res.iter().zip(expected.iter()) {
///     assert_eq!(r,e);
/// }
/// ```
pub fn decode(g6: &str) -> Result<Vec<u64>, InvalidBinary> {
    let capa = (((g6.len() * 6) as f64) / 64.).ceil() as usize;
    let mut res = Vec::with_capacity(capa);
    if !g6.is_empty() {
        let data = g6.as_bytes();
        let mut cur = [0u8; 8];
        let mut pdata = 0;
        let mut p = 0;
        let mut v: u64 = 0;
        while pdata < data.len() {
            // We take 4 chars or as many available
            for _ in 0..4 {
                v <<= 6;
                if pdata < data.len() {
                    v += u64::from(data[pdata])
                        .checked_sub(63)
                        .ok_or(InvalidBinary::new(&format!(
                            "Incorrect value when decoding {}.",
                            g6
                        )))?;
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
    Ok(res)
}

#[repr(C)]
pub struct Converter {
    ws: u64,
    mask: u64,
    needed_p: usize,
    needed: u64,
    word_needed: u64,
    word_res: u64,
    added: u64,
    scheme: Vec<u64>,
    result: Vec<u64>,
}

impl Converter {
    fn with_ws(scheme: &[u64], ws: u64) -> Converter {
        let needed = if !scheme.is_empty() { scheme[0] } else { 0 };
        Converter {
            ws: ws,
            mask: (((1 << (ws - 1)) - 1) << 1) + 1,
            needed_p: 0,
            needed: needed,
            word_needed: std::cmp::min(ws, needed),
            word_res: 0,
            added: 0,
            scheme: scheme.into(),
            result: Vec::new(),
        }
    }

    pub fn new(scheme: &[u64]) -> Converter {
        Converter::with_ws(scheme, 64)
    }

    /// Add nbits bits of data to the converter.
    pub fn feed(&mut self, nbits: u64, data: &[u64]) {
        // If we still need data and there is actual data
        if !data.is_empty() && nbits > 0 && self.needed > 0 {
            let mut remaining = nbits;
            let mut word_remaining = std::cmp::min(self.ws, remaining);
            let mut p = 0;
            let mut word = data[p];
            let mut to_take;
            let mut val;
            // We consume all the data except if there's too much
            while remaining > 0 {
                // How much data we can add in the current word or take from the current word
                to_take = std::cmp::min(self.word_needed, word_remaining);
                val = word >> (self.ws - to_take);
                self.word_res |= val << (self.ws - to_take - self.added);
                word = word.wrapping_shl(to_take as u32) & self.mask;
                self.word_needed -= to_take;
                self.needed -= to_take;
                word_remaining -= to_take;
                remaining -= to_take;
                self.added += to_take;
                // If we cannot add data to the current word
                if self.word_needed == 0 {
                    self.result.push(self.word_res);
                    self.word_res = 0;
                    self.added = 0;
                    if self.needed == 0 {
                        self.needed_p += 1;
                        if self.needed_p < self.scheme.len() {
                            self.needed = self.scheme[self.needed_p];
                        } else {
                            // If we have all the needed data, we can stop
                            return;
                        }
                    }
                    self.word_needed = std::cmp::min(self.needed, self.ws);
                }
                if word_remaining == 0 && remaining > 0 {
                    word_remaining = std::cmp::min(remaining, self.ws);
                    p += 1;
                    word = data[p]; // If out of bounds, input error
                }
            }
        }
    }

    pub fn result(mut self) -> Vec<u64> {
        while self.needed > 0 {
            self.feed(64, &[0]);
        }
        self.result
    }
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

    #[test]
    fn test_convert() {
        let mut converter = Converter::with_ws(&[2, 2, 2, 2, 2], 2);
        converter.feed(1, &[0b10]);
        converter.feed(2, &[0b11]);
        converter.feed(3, &[0b11, 0b10]);
        converter.feed(4, &[0b11, 0b11]);
        let mut res = converter.result();
        assert_eq!(5, res.len(), "same length");
        for (i, &r) in res.iter().enumerate() {
            assert_eq!(3, r, "{} same value", i);
        }

        converter = Converter::with_ws(&[1, 2, 3, 4], 2);
        converter.feed(2, &[0b11]);
        converter.feed(2, &[0b11]);
        converter.feed(2, &[0b11]);
        converter.feed(2, &[0b11]);
        converter.feed(2, &[0b11]);
        res = converter.result();
        let expected = [0b10, 0b11, 0b11, 0b10, 0b11, 0b11];
        assert_eq!(6, res.len(), "same length");
        for (i, (&e, &r)) in res.iter().zip(expected.iter()).enumerate() {
            assert_eq!(e, r, "{} same value", i);
        }
        converter = Converter::new(&[64]);
        converter.feed(2, &[0b11 << 62]);
        converter.feed(4, &[0b1111 << 60]);
        converter.feed(6, &[0b111111 << 58]);
        converter.feed(8, &[0b11111111 << 56]);
        converter.feed(10, &[0b1111111111 << 54]);
        res = converter.result();
        assert_eq!(1, res.len());
        assert_eq!(0xfffffffc << 32, res[0]);
    }
}
