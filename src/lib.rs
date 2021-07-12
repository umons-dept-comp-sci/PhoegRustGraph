//! Crate using binary format to represent small graphs (order <= 11)

//#![feature(trace_macros)]

extern crate base64;
extern crate bit_vec;
extern crate libc;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate doc_comment;

pub mod errors;
pub mod format;
pub mod invariants;
pub mod nauty;
#[macro_use]
mod transfos_macros;
pub mod algorithm;
pub mod subgraphs;
pub mod transfo_result;
pub mod transfos;

use errors::InvalidBinary;
use std::fmt;

#[allow(non_camel_case_types)]
type set = libc::c_ulonglong;

#[allow(non_camel_case_types)]
// Type used by nauty in C
type int = libc::c_int;
#[allow(non_camel_case_types)]
type graph = set;

mod detail {
    use super::graph;
    use super::int;
    use super::set;
    extern "C" {
        pub fn setwordsneeded(n: int) -> int;
        pub fn emptyset(input: *mut set, size: int);
        pub fn addelement(input: *mut set, elem: int);
        pub fn delelement(input: *mut set, elem: int);
        pub fn flipelement(input: *mut set, elem: int);
        pub fn iselement(input: *const set, elem: int) -> bool;
        #[allow(dead_code)]
        pub fn setsize(input: *const set, size: int) -> int;
        pub fn nextelement(input: *const set, size: int, pos: int) -> int;
        pub fn wordsize() -> int;
        pub fn allbits() -> set;
        pub fn allmask(i: int) -> set;
        #[allow(dead_code)]
        pub fn emptygraph(graph: *mut graph, m: int, n: int);
        pub fn graphrow(graph: *const graph, v: int, m: int) -> *const set;
        pub fn graphrowmut(graph: *mut graph, v: int, m: int) -> *mut set;
        pub fn addoneedge(graph: *mut graph, v: int, w: int, m: int);
        pub fn sublabel(
            graph: *mut graph,
            perm: *const int,
            nperm: int,
            workg: *mut graph,
            m: int,
            n: int,
        );
    }
    pub fn complement_set(s: *mut set, len: u64, maxm: u64) {
        if len > 0 {
            let mut s = s;
            let mut maxm = maxm;
            unsafe {
                for _ in 0..(len - 1) {
                    *s = !*s;
                    maxm -= wordsize() as u64;
                    s = s.add(1);
                }
                *s = !*s & allmask(maxm as int);
            }
        }
    }
}

/// Structure to store a set of integers using binary words.
/// This structure can store all integers from 0 to a maximum value given in parameters to the
/// constructors. For example, a maximum value of 16 allows storing all integers from 0 to 15.
/// Since it uses 64 bits binary words, a maximum size of 64 allows using only one word and is thus
/// faster.
#[repr(C)]
#[derive(Clone, Debug)]
pub struct Set {
    data: Vec<set>,
    maxm: u64,
    size: u64,
}

impl Set {
    fn initfill<PF>(maxelem: u64, pfunc: PF, val: set, numelem: u64) -> Set
    where
        PF: Fn(u64) -> set,
    {
        unsafe {
            if maxelem > 0 {
                let mut p = maxelem;
                let words = detail::setwordsneeded(maxelem as int) as u64;
                let mut v = Vec::with_capacity(words as usize);
                for _ in 0..words - 1 {
                    v.push(val);
                    p -= detail::wordsize() as u64;
                }
                v.push(pfunc(p));
                Set {
                    data: v,
                    maxm: maxelem,
                    size: numelem,
                }
            } else {
                Set {
                    data: vec![],
                    maxm: 0,
                    size: 0,
                }
            }
        }
    }

    /// Returns an empty set that can contain elements up to `max`-1 (from 0 to `max`-1).
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(0);
    /// assert_eq!(s.size(),0);
    /// s = Set::new(112);
    /// assert_eq!(s.size(), 0);
    /// for i in 0..112 {
    ///     assert!(!s.contains(i));
    /// }
    /// ```
    pub fn new(max: u64) -> Set {
        Set::initfill(max, |_| 0, 0, 0)
    }

    /// Returns a set with with all the elements from 0 to `max`-1.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::full(112);
    /// assert_eq!(s.size(),112);
    /// for i in 0..112 {
    ///     assert!(s.contains(i));
    /// }
    /// ```
    pub fn full(max: u64) -> Set {
        unsafe { Set::initfill(max, |x| detail::allmask(x as int), detail::allbits(), max) }
    }

    /// Removes all elements from the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::full(112);
    /// s.clear();
    /// assert_eq!(s.size(),0);
    /// for i in 0..112 {
    ///     assert!(!s.contains(i));
    /// }
    /// ```
    pub fn clear(&mut self) {
        unsafe {
            self.size = 0;
            detail::emptyset(self.data.as_mut_ptr(), self.data.len() as int)
        }
    }

    /// Adds all possible elements to the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(112);
    /// s.add(34);
    /// s.add(100);
    /// s.fill();
    /// assert_eq!(s.size(), 112);
    /// for i in 0..112 {
    ///     assert!(s.contains(i));
    /// }
    /// ```
    pub fn fill(&mut self) {
        if self.maxm > 0 {
            unsafe {
                let p = detail::setwordsneeded(self.maxm as int);
                let mut rem = self.maxm as u64;
                for i in 0..p - 1 {
                    self.data[i as usize] = detail::allbits();
                    rem -= detail::wordsize() as u64;
                }
                *self.data.last_mut().unwrap() = detail::allmask(rem as int);
                self.size = self.maxm;
            }
        }
    }

    /// Adds element `elem` to the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(112);
    /// let elems: Vec<u64> = vec![0,34,67,111];
    /// for i in &elems {
    ///     s.add(*i);
    /// }
    /// assert_eq!(s.size(),elems.len() as u64);
    /// for &i in &elems {
    ///     assert!(s.contains(i));
    /// }
    /// assert!(std::panic::catch_unwind(move || s.add(112)).is_err());
    /// ```
    ///
    /// Panics :
    /// if `elem > set.getmax()`
    pub fn add(&mut self, elem: u64) {
        assert!(elem < self.maxm);
        if !self.contains(elem) {
            self.size += 1;
            unsafe { detail::addelement(self.data.as_mut_ptr(), elem as int) }
        }
    }

    /// Removes element `elem` from the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::full(112);
    /// let elems: Vec<u64> = vec![0,34,67,111];
    /// for i in &elems {
    ///     s.remove(*i);
    /// }
    /// assert_eq!(s.size(),112-elems.len() as u64);
    /// for &i in &elems {
    ///     assert!(!s.contains(i));
    /// }
    /// assert!(std::panic::catch_unwind(move || s.remove(112)).is_err());
    /// ```
    ///
    /// Panics :
    /// if `elem > set.getmax()`
    pub fn remove(&mut self, elem: u64) {
        assert!(elem < self.maxm);
        if self.contains(elem) {
            self.size -= 1;
            unsafe { detail::delelement(self.data.as_mut_ptr(), elem as int) }
        }
    }

    /// Toggles element `elem` from the set.
    /// i.e., if `elem` was in the set, it is removed, if it was not int the set, it is added.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(112);
    /// let outside: Vec<u64> = vec![2,6,74,107];
    /// for i in &outside {
    ///     s.add(*i);
    /// }
    /// let inside: Vec<u64> = vec![0,34,67,81,111];
    /// for i in inside.iter().chain(outside.iter()) {
    ///     s.flip(*i);
    /// }
    /// assert_eq!(s.size(),inside.len() as u64);
    /// for i in &outside {
    ///     assert!(!s.contains(*i));
    /// }
    /// for i in &inside {
    ///     assert!(s.contains(*i));
    /// }
    /// assert!(std::panic::catch_unwind(move || s.flip(112)).is_err());
    /// ```
    ///
    /// Panics :
    /// if `elem > set.getmax()`
    pub fn flip(&mut self, elem: u64) {
        assert!(elem < self.maxm);
        unsafe {
            if self.contains(elem) {
                self.size -= 1;
            } else {
                self.size += 1;
            }
            detail::flipelement(self.data.as_mut_ptr(), elem as int)
        }
    }

    /// Returns `true` if the set contains `elem` and `false` otherwise.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut elems = vec![0,4,1,10,9,66,74,7];
    /// let s: Set = elems.as_slice().into();
    /// elems.sort();
    /// assert_eq!(s.size(),8);
    /// assert_eq!(s.getmax(),75);
    /// let mut p = 0;
    /// for i in 0..75 {
    ///     if i == elems[p] {
    ///         assert!(s.contains(i));
    ///         p += 1;
    ///     } else {
    ///         assert!(!s.contains(i));
    ///     }
    /// }
    /// ```
    ///
    /// Panics :
    /// if `elem > set.getmax()`
    pub fn contains(&self, elem: u64) -> bool {
        assert!(elem < self.maxm);
        unsafe { detail::iselement(self.data.as_ptr(), elem as int) }
    }

    /// Returns the number of elements in the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(154);
    /// assert_eq!(s.size(),0);
    /// s.add(0);
    /// s.add(10);
    /// s.add(130);
    /// assert_eq!(s.size(),3);
    /// s.fill();
    /// assert_eq!(s.size(),154);
    /// s.clear();
    /// assert_eq!(s.size(),0);
    /// ```
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Returns an iterator over the elements of the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let elements: &[u64] = &[3,9,25,66];
    /// let mut s: Set = elements.into();
    /// for (i,e) in s.iter().enumerate() {
    ///     assert_eq!(e,elements[i]);
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        SetIter::new(self.data.as_ptr(), self.data.len() as u64)
    }

    /// Returns the maximum number of elements that the set can contain.
    /// Note that this is also the maximum element that can be added.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(0);
    /// assert_eq!(s.getmax(),0);
    /// s = Set::new(23);
    /// assert_eq!(s.getmax(),23);
    /// ```
    pub fn getmax(&self) -> u64 {
        self.maxm
    }

    /// Changes the maximum value that can be stored in the set and the maximum size of the set.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut set = Set::full(112);
    /// set.remove(7);
    /// set.setmax(20);
    /// assert_eq!(set.size(),19);
    /// assert_eq!(set.getmax(),20);
    /// for i in 0..20 {
    ///     if i != 7 {
    ///         assert!(set.contains(i));
    ///     } else {
    ///         assert!(!set.contains(i));
    ///     }
    /// }
    /// set.setmax(120);
    /// assert_eq!(set.size(),19);
    /// assert_eq!(set.getmax(),120);
    /// for i in 0..120 {
    ///     if i < 20 && i != 7 {
    ///         assert!(set.contains(i));
    ///     } else {
    ///         assert!(!set.contains(i));
    ///     }
    /// }
    /// set.fill();
    /// assert_eq!(set.size(),120);
    /// assert_eq!(set.getmax(),120);
    /// for i in 0..120 {
    ///     assert!(set.contains(i));
    /// }
    /// ```
    pub fn setmax(&mut self, nmax: u64) {
        unsafe {
            if self.maxm != nmax {
                let words = self.data.len() as u64;
                let nw = detail::setwordsneeded(nmax as int) as u64;
                if nw == 0 {
                    self.data.clear();
                    self.maxm = nmax;
                    self.size = 0;
                } else if nmax < self.maxm {
                    if nw < words {
                        let diff = words - nw;
                        for _ in 0..diff {
                            self.data.pop();
                            self.maxm -= detail::wordsize() as u64;
                        }
                    }
                    let rem = nmax - (nw - 1) * detail::wordsize() as u64;
                    {
                        let lst = self.data.last_mut().unwrap();
                        *lst &= detail::allmask(rem as int) as set;
                    }
                    self.size = detail::setsize(self.data.as_ptr(), nw as int) as u64;
                } else if nw > words {
                    let diff = nw - words;
                    for _ in 0..diff {
                        self.data.push(0);
                    }
                }
                self.maxm = nmax;
            }
        }
    }

    fn combine<C>(first: &mut Set, other: &Set, comb: C)
    where
        C: Fn(&set, &set) -> set,
    {
        for (i, a) in first
            .data
            .iter_mut()
            .enumerate()
            .take_while(|(i, _)| other.data.len() > *i)
        {
            *a = comb(a, &other.data[i]);
        }
    }

    /// Removes the elements in the set that are not present in the other set.
    /// If you do not want your set to be modified, make a copy first.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s1: Set = vec![3,8,0,123].as_slice().into();
    /// let mut s2: Set = vec![5,12,0,123].as_slice().into();
    /// s1.inter(&s2);
    /// assert_eq!(s1.size(),2);
    /// for &i in &[0,123] {
    ///     assert!(s1.contains(i as u64));
    /// }
    /// for &i in &[3,8,12] {
    ///     assert!(!s1.contains(i as u64));
    /// }
    /// s1 = vec![3,8,0,123].as_slice().into();
    /// s2 = vec![].as_slice().into();
    /// s1.inter(&s2);
    /// assert_eq!(s1.size(),0);
    /// for &i in &[0,3,8,123] {
    ///     assert!(!s1.contains(i as u64));
    /// }
    /// ```
    pub fn inter(&mut self, other: &Set) {
        Set::combine(self, other, |a, b| a & b);
        if self.data.len() > other.data.len() {
            for i in other.data.len()..self.data.len() {
                self.data[i] = 0;
            }
        }
        unsafe {
            self.size = detail::setsize(self.data.as_ptr(), self.data.len() as int) as u64;
        }
    }

    /// Adds all the elements from the other set to this set.
    /// If you do not want your set to be modified, make a copy first.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s1: Set = vec![3,8,0,123].as_slice().into();
    /// let mut s2: Set = vec![5,12,0,123].as_slice().into();
    /// s1.union(&s2);
    /// assert_eq!(s1.size(),6);
    /// for &i in &[0,3,5,8,12,123] {
    ///     assert!(s1.contains(i as u64));
    /// }
    /// s2 = vec![].as_slice().into();
    /// s2.union(&s1);
    /// assert_eq!(s2.size(),6);
    /// for &i in &[0,3,5,8,12,123] {
    ///     assert!(s2.contains(i as u64));
    /// }
    /// ```
    pub fn union(&mut self, other: &Set) {
        if self.data.len() < other.data.len() {
            for _ in self.data.len()..other.data.len() {
                self.data.push(0);
            }
        }
        self.maxm = std::cmp::max(self.maxm, other.maxm);
        Set::combine(self, other, |&a, &b| a | b);
        unsafe {
            self.size = detail::setsize(self.data.as_ptr(), self.data.len() as int) as u64;
        }
    }

    /// Flips every element of the set. i.e., each element between 0 and max-1 that was in the set
    /// is removed and every other element is added.
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut s = Set::new(0);
    /// s.complement();
    /// assert_eq!(s.size(),0);
    /// s = vec![1,3,6,333].as_slice().into();
    /// s.complement();
    /// assert_eq!(s.size(),334-4);
    /// ```
    pub fn complement(&mut self) {
        detail::complement_set(self.data.as_mut_ptr(), self.data.len() as u64, self.maxm);
        self.size = self.maxm - self.size;
    }
}

impl fmt::Display for Set {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.iter().collect::<Vec<u64>>())
    }
}

impl<'a> From<&'a [u64]> for Set {
    /// Converts a slice to a Set
    ///
    /// Examples :
    /// ```
    /// use graph::Set;
    /// let mut elems = vec![0,4,1,10,9,66,74,7];
    /// let s: Set = elems.as_slice().into();
    /// elems.sort();
    /// assert_eq!(s.size(),8);
    /// assert_eq!(s.getmax(),75);
    /// let mut p = 0;
    /// for i in 0..75 {
    ///     if i == elems[p] {
    ///         assert!(s.contains(i));
    ///         p += 1;
    ///     } else {
    ///         assert!(!s.contains(i));
    ///     }
    /// }
    /// ```
    fn from(slice: &[u64]) -> Self {
        let mut set = Set::new(0);
        for &i in slice {
            if i >= set.getmax() {
                set.setmax(i + 1);
            }
            set.add(i);
        }
        set
    }
}

impl std::iter::IntoIterator for Set {
    type Item = u64;
    type IntoIter = SetIter;

    fn into_iter(self) -> Self::IntoIter {
        SetIter::new(self.data.as_ptr(), self.data.len() as u64)
    }
}

#[repr(C)]
#[derive(Clone)]
pub struct SetIter {
    data: *const set,
    len: u64,
    pos: i64,
}

impl SetIter {
    fn new(data: *const set, len: u64) -> SetIter {
        SetIter::with_pos(data, len, -1i64)
    }

    fn with_pos(set: *const set, numelem: u64, start: i64) -> SetIter {
        SetIter {
            data: set,
            len: numelem,
            pos: start,
        }
    }
}

impl Iterator for SetIter {
    type Item = u64;

    fn next(&mut self) -> Option<u64> {
        unsafe {
            let p = detail::nextelement(self.data, self.len as int, self.pos as int);
            self.pos = i64::from(p);
            if self.pos < 0 {
                None
            } else {
                Some(self.pos as u64)
            }
        }
    }
}

pub trait Graph: Sized {
    fn new(n: u64) -> Self;
    fn order(&self) -> u64;
    fn size(&self) -> u64;
    fn add_vertex(&mut self);
    fn remove_vertex(&mut self, i: u64);
    fn is_vertex(&self, u: u64) -> bool;
    fn is_edge(&self, u: u64, w: u64) -> bool;
    fn add_edge(&mut self, u: u64, w: u64);
    fn remove_edge(&mut self, u: u64, w: u64);

    fn complement(&self) -> Self {
        let mut res = Self::new(self.order());
        for i in 1..self.order() {
            for j in 0..i {
                if !self.is_edge(i, j) {
                    res.add_edge(i, j);
                }
            }
        }
        res
    }

    fn add_cycle(&mut self, lst: &[u64]) {
        for (&i, &j) in lst.iter().zip(lst.iter().cycle().skip(1)) {
            self.add_edge(i, j);
        }
    }

    fn is_cycle(&self, lst: &[u64]) -> bool {
        lst.iter()
            .zip(lst.iter().cycle().skip(1))
            .all(|(&x, &y)| self.is_edge(x, y))
    }

    /// Returns true if each neighbor of u (ignoring v) is also adjacent to v and u has at least
    /// one neighbor that is not v.
    fn are_twins(&self, u: u64, v: u64) -> bool {
        let mut n = 0;
        for i in 0..self.order() {
            if i != u && i != v && self.is_edge(u, i) {
                n += 1;
                if !self.is_edge(v, i) {
                    return false;
               }
            }
        }
        n > 0
    }

    /// Returns true if all the neighbors of u (v not included) are also neighbors of v. Note that
    /// we consider that u must have at least a neighbor that is not v.
    fn is_neighborhood_included(&self, u: u64, v: u64) -> bool {
        let mut n = 0;
        for i in 0..self.order() {
            if i != u && i != v && self.is_edge(u, i) {
                n += 1;
                if !self.is_edge(v, i) {
                    return false;
                }
            }
        }
        n > 0
    }

    /// Contracts two vertices in a single one.
    /// # Examples:
    /// ```
    /// use graph::format::from_g6;
    /// use graph::GraphFormat;
    /// use graph::Graph;
    /// use graph::GraphNauty;
    /// let g: GraphNauty = from_g6("FWCWw").unwrap();
    /// let g = g.contract(0, 2);
    /// let expected: GraphNauty = from_g6("E`Kw").unwrap();
    /// assert_eq!(g.order(), expected.order(), "order");
    /// assert_eq!(g.size(), expected.size(), "size");
    /// for i in 1..g.order() {
    ///     for j in 0..i {
    ///         assert_eq!(g.is_edge(i,j), expected.is_edge(i,j), "edge {} {}", i, j);
    ///     }
    /// }
    /// ```
    fn contract(&self, u: u64, v: u64) -> Self {
        //TODO check u and v ok and maybe panic ?
        let mut res = Self::new(self.order() - 1);
        let u = std::cmp::min(u, v);
        let v = std::cmp::max(u, v);
        for i in 1..self.order() {
            for j in 0..i {
                if j != u || i != v {
                    if self.is_edge(i, j) {
                        let i = if i > v { i - 1 } else if i == v { u } else {i};
                        let j = if j > v { j - 1 } else if j == v { u } else {j};
                        res.add_edge(i, j);
                    }
                }
            }
        }
        res
    }
}

//pub trait GraphIter: Graph {
pub trait GraphIter: Graph {
    type VertIter: Iterator<Item = u64> + Clone;
    //type EdgeIter: Iterator<Item=(u64,u64)>;
    type NeighIter: Iterator<Item = u64> + Clone;
    fn vertices(&self) -> Self::VertIter;
    //fn edges(&'a self) -> Self::EdgeIter;
    fn neighbors(&self, u: u64) -> Self::NeighIter;
}

pub trait GraphFormat: Graph {
    fn to_bin(&self) -> Vec<u64>;
    fn from_bin(data: &[u64]) -> Result<Self, InvalidBinary>;
}

pub trait GraphIso: Graph {
    fn canon_fixed(&self, fixed: &[Vec<u64>]) -> (Self, Vec<u64>, Vec<u64>);
    fn canon(&self) -> (Self, Vec<u64>, Vec<u64>) {
        self.canon_fixed(&[])
    }
    fn orbits(&self, fixed: &[Vec<u64>]) -> Vec<u64>;
}

/// Structure representing a undirected simple graph.
#[repr(C)]
#[derive(Clone)]
pub struct GraphNauty {
    data: Vec<graph>,
    n: u64,
    m: u64,
    w: u64,
}

impl GraphNauty {

    /// Compares two lines of the adjacency matrix using a given closure. The closure will be
    /// called on each pair of blocks of the lines and the function returns false if the closure
    /// returns false once or if u has no neighbor that is not v.
    ///
    /// # Examples
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(6);
    /// for x in (1..5) {
    ///     g.add_edge(0,x);
    ///     g.add_edge(5,x);
    /// }
    /// g.add_edge(0,5);
    /// assert!(g.are_twins(0,5),"basic test");
    /// g.remove_edge(0,5);
    /// assert!(g.are_twins(0,5),"not connected");
    /// g.add_edge(0,5);
    /// g.remove_edge(1,5);
    /// assert!(!g.are_twins(0,5),"neighbor removed from one");
    /// g.remove_edge(1,0);
    /// assert!(g.are_twins(0,5),"neighbor removed from both");
    /// g = GraphNauty::new(30);
    /// for i in 0..29 {
    ///     for j in i+1..30 {
    ///        g.add_edge(i,j);
    ///     }
    /// }
    /// assert!(g.are_twins(5,29),"big graph");
    /// g.remove_edge(5,29);
    /// assert!(g.are_twins(5,29),"big graph, not connected");
    /// g.remove_edge(5,28);
    /// assert!(!g.are_twins(5,29),"big graph, not twins");
    /// ```
    fn compare_matrix_lines<F>(&self, u: u64, v: u64, comp: F) -> bool
        where F: Fn(set, set) -> bool
    {
        unsafe {
            let (mut u, mut v) = (u, v); //We need to change them later
            let mut other_neighbor = false; //
            let (mut udone, mut vdone) = (false, false);
            let urow = std::slice::from_raw_parts(
                detail::graphrow(self.data.as_ptr(), u as int, self.w as int),
                self.w as usize,
            );
            let vrow = std::slice::from_raw_parts(
                detail::graphrow(self.data.as_ptr(), v as int, self.w as int),
                self.w as usize,
            );
            for i in 0..self.w {
                let mut up = urow[i as usize];
                let mut vp = vrow[i as usize];
                // We could just compare the two rows if they had loops. So we add loops and
                // connect them for the comparison.
                if !udone && u < 64 {
                    up &= !(1 << (63 - u));
                    vp &= !(1 << (63 - u));
                    udone = !udone;
                }
                if !vdone && v < 64 {
                    up &= !(1 << (63 - v));
                    vp &= !(1 << (63 - v));
                    vdone = !vdone;
                }
                other_neighbor |= up > 0;
                if !comp(up, vp) {
                    return false;
                }
                u = u.saturating_sub(64);
                v = v.saturating_sub(64);
            }
            return other_neighbor;
        }
    }

    /// # Examples
    ///
    /// ```
    /// use graph::Graph;
    /// use graph::GraphNauty;
    /// use graph::format;
    /// use graph::errors::*;
    /// let mut g: GraphNauty;
    /// g = GraphNauty::parse_graph6(&"?".to_string());
    /// assert!(g.order() == 0);
    /// g = GraphNauty::parse_graph6(&"@".to_string());
    /// assert!(g.order() == 1);
    /// g = GraphNauty::parse_graph6(&"A?".to_string());
    /// assert!(g.order() == 2);
    /// assert!(!g.is_edge(0,1));
    /// g = GraphNauty::parse_graph6(&"A_".to_string());
    /// assert!(g.order() == 2);
    /// assert!(g.is_edge(0,1));
    /// g = GraphNauty::parse_graph6(&"JhCGGC@?G?_".to_string());
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
    /// ```
    pub fn parse_graph6(s: &str) -> Self {
        let mut chars = s.chars();
        let mut n = (chars.next().unwrap() as u64).checked_sub(63).unwrap();
        if n > 62 { // The first byte read was 126 which means we use 126 R(x)
            n = chars.by_ref().take(3).fold(0, |n, b| (n << 6) | ((b as u64).checked_sub(63).unwrap()));
        }
        if n > 258047 { // The second byte read was 126 which means we use 126 126 R(x) and not 126 R(x)
            n &= 4095; // Remove the second 126 (the first was ignored in the previous if)
            n = chars.by_ref().take(4).fold(n, |n, b| (n << 6) | ((b as u64).checked_sub(63).unwrap()));
        }
        let mut g = GraphNauty::new(n);
        let mut k = 1;
        let mut x = 0;
        for j in 1..n {
            for i in 0..j {
                k -= 1;
                if k == 0 {
                    k = 6;
                    x = (chars.next().unwrap() as u8).checked_sub(63).unwrap();
                }
                if (x & 32u8) > 0 {
                    g.add_edge(i, j);
                }
                x = x.wrapping_shl(1);
            }
        }
        g
    }
}

impl GraphFormat for GraphNauty {
    /// Returns a minimal binary form of the graph
    ///
    /// # Examples
    ///
    /// ```
    /// //TODO Update tests
    /// use graph::{Graph,GraphNauty,GraphFormat};
    /// let mut n = 5;
    /// let mut g = GraphNauty::new(n);
    /// g.add_cycle(&((0..n).collect::<Vec<u64>>()));
    /// let mut res = g.to_bin();
    /// let expected = [0x1699000000000000];
    /// assert_eq!(res.len(),expected.len());
    /// for (e,r) in expected.iter().zip(res.iter()) {
    ///     assert_eq!(e,r);
    /// }
    /// n = 30;
    /// g = GraphNauty::new(n);
    /// g.add_cycle(&((0..n).collect::<Vec<u64>>()));
    /// res = g.to_bin();
    /// let expected = [0x7a91082040402008,
    ///                     0x0100100080020004,
    ///                     0x0004000200008000,
    ///                     0x1000010000080000,
    ///                     0x2000004000004000,
    ///                     0x0020000008000001,
    ///                     0x0000001800000080];
    /// assert_eq!(res.len(),expected.len());
    /// for (e,r) in expected.iter().zip(res.iter()) {
    ///     assert_eq!(e,r);
    /// }
    /// g = GraphNauty::new(142);
    /// res = g.to_bin();
    /// assert_eq!(0xfc008e0000000000,res[0]);
    /// ```
    fn to_bin(&self) -> Vec<u64> {
        let mut res = vec![];
        // First step : encode order of the graph
        let mut cur = 0;
        let mut dec = if self.n >= 258_048 {
            cur |= 4095 << 52;
            16
        } else if self.n >= 63 {
            cur |= 63 << 58;
            40
        } else {
            58
        };
        cur |= self.n << dec;
        let mut to_take = 1;
        let mut to_add;
        let mut rem;
        let mut lp;
        let mut taken;
        // for each vertex
        for p in (1..self.n).map(|x| x * self.w) {
            lp = 0;
            rem = to_take;
            while rem > 0 {
                //  if we can get a full 64 bit, we take them
                if rem > 64 {
                    to_add = self.data[(p + lp) as usize];
                    lp += 1;
                    taken = 64;
                    rem -= 64;
                }
                //  otherwise, we take all the available ones
                else {
                    to_add = self.data[(p + lp) as usize].wrapping_shr(64 - rem as u32);
                    taken = rem;
                    rem = 0;
                }
                //  then we add these bits to cur
                //  if there is too much to fit in the remaining bits in cur,
                if taken > dec {
                    //  we add as much as we can to cur,
                    cur |= to_add.wrapping_shr(taken - dec);
                    //  add it to res,
                    res.push(cur);
                    //  make cur a new u64
                    cur = 0;
                    taken -= dec;
                    dec = 64;
                    to_add &= (1u64 << taken) - 1;
                }
                cur |= to_add << (dec - taken);
                dec -= taken;
                if dec == 0 {
                    res.push(cur);
                    cur = 0;
                    dec = 64;
                }
            }
            //  take one more bit each time
            to_take += 1;
        }
        if dec < 64 {
            res.push(cur);
        }
        res
    }

    /// Returns a minimal binary form of the graph
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty,GraphFormat};
    /// let data = [0x1699000000000000];
    /// let mut n = 5;
    /// let mut g = graph::GraphNauty::from_bin(&data).unwrap();
    /// assert_eq!(n,g.order());
    /// assert!(g.is_cycle(&((0..n).collect::<Vec<u64>>())));
    /// let data = [0x7a91082040402008,
    ///                     0x0100100080020004,
    ///                     0x0004000200008000,
    ///                     0x1000010000080000,
    ///                     0x2000004000004000,
    ///                     0x0020000008000001,
    ///                     0x0000001800000080];
    /// n = 30;
    /// let mut g = graph::GraphNauty::from_bin(&data).unwrap();
    /// assert_eq!(n,g.order());
    /// assert!(g.is_cycle(&((0..n).collect::<Vec<u64>>())));
    /// let data = [0xfc008e0000000000];
    /// let res = graph::GraphNauty::from_bin(&data);
    /// assert!(res.is_err());
    /// ```
    fn from_bin(data: &[u64]) -> Result<GraphNauty, InvalidBinary> {
        if !data.is_empty() {
            let n;
            let mut cur = data[0];
            let mut rem;
            if (cur.wrapping_shr(58)) == 63 {
                if (cur.wrapping_shr(52)) == 4095 {
                    n = (cur.wrapping_shr(16)) & ((1 << 36) - 1);
                    cur &= (1 << 48) - 1;
                    rem = 48;
                } else {
                    n = (cur.wrapping_shr(40)) & ((1 << 18) - 1);
                    cur &= (1 << 24) - 1;
                    rem = 24;
                }
            } else {
                n = cur.wrapping_shr(58);
                cur &= (1 << 58) - 1;
                rem = 58;
            }
            let mut g = GraphNauty::new(n);
            let mut p = 0;
            // For each vertex
            for i in 1..n {
                // For each other vertex before this one
                for j in 0..i {
                    // if we reach the end of the current number
                    // get the next one
                    // if there's no next one, error
                    if rem == 0 && p < data.len() - 1 {
                        p += 1;
                        cur = data[p];
                        rem = 64;
                    } else if rem == 0 && p >= data.len() - 1 {
                        return Err(InvalidBinary::new("Not enough data"));
                    }
                    // if the bit is set
                    if cur.wrapping_shr(rem - 1) == 1 {
                        // add an edge
                        g.add_edge(i, j);
                    }
                    rem -= 1;
                    cur &= (1 << rem) - 1;
                }
            }
            Ok(g)
        } else {
            Err(InvalidBinary::new("Not enough data"))
        }
    }
}

impl Graph for GraphNauty {
    /// Constructs a new graph with 0 edges and n vertices.
    fn new(ord: u64) -> GraphNauty {
        unsafe {
            let words = detail::setwordsneeded(ord as int) as u64;
            let v = vec![0; (ord * words) as usize];
            GraphNauty {
                data: v,
                n: ord,
                m: 0,
                w: words,
            }
        }
    }

    /// Returns the order of the graph
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(0);
    /// assert!(g.order() == 0);
    /// for _ in 0..11
    /// {
    ///     g.add_vertex();
    /// }
    /// assert!(g.order() == 11);
    /// ```
    fn order(&self) -> u64 {
        self.n
    }

    /// Returns the size of the graph
    ///
    /// #Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(11);
    /// assert!(g.size() == 0);
    /// for i in 1..11
    /// {
    ///     for j in 0..i
    ///     {
    ///         g.add_edge(i,j);
    ///     }
    /// }
    /// assert!(g.size() == 11*10/2);
    /// ```
    fn size(&self) -> u64 {
        self.m
    }

    /// Adds a new vertex to the graph, increasing its order by one.
    /// Will return false if the graph had already an order of 11.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(0);
    /// assert!(g.order() == 0);
    /// for i in 0..11
    /// {
    ///     g.add_vertex();
    ///     assert!(g.order() == i+1);
    /// }
    /// ```
    fn add_vertex(&mut self) {
        unsafe {
            let neww = detail::setwordsneeded((self.n + 1) as int) as u64;
            if neww > self.w {
                let mut newdata: Vec<graph> = Vec::with_capacity(((self.n + 1) * neww) as usize);
                let mut p = self.w;
                for d in self.data.drain(..) {
                    newdata.push(d);
                    p -= 1;
                    if p == 0 {
                        newdata.push(0); //The increase can only be one since we only add one
                                         // vertex
                        p = self.w;
                    }
                }
                self.data = newdata;
                self.w = neww;
            }
            self.data.push(0);
            self.n += 1;
        }
    }

    // [TODO]: Add unit tests for this.
    /// Removes the vertex i from the graph. The order if the vertices is not conserved.
    /// The last vertex takes the place of the removed one.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty,GraphIter};
    /// let mut g = GraphNauty::new(7);
    /// for i in g.vertices().skip(1) {
    ///     g.add_edge(i-1,i);
    /// }
    /// g.remove_vertex(7);
    /// assert_eq!(g.order(),7);
    /// g.remove_vertex(6);
    /// assert_eq!(g.order(),6);
    /// g.remove_vertex(0);
    /// assert_eq!(g.order(),5);
    /// g.remove_vertex(3);
    /// assert_eq!(g.order(),4);
    /// ```
    fn remove_vertex(&mut self, i: u64) {
        if self.n > i {
            unsafe {
                let n = self.n;
                for u in 0..n {
                    if u != i {
                        self.remove_edge(u, i);
                    }
                }
                let mut workg = vec![0; (self.n * self.w) as usize];
                let perm: Vec<int> = (0..(self.n as int)).filter(|&x| x != i as int).collect();
                detail::sublabel(
                    self.data.as_mut_ptr(),
                    perm.as_ptr(),
                    perm.len() as int,
                    workg.as_mut_ptr(),
                    self.w as int,
                    self.n as int,
                );
                self.n -= 1;
                self.w = detail::setwordsneeded(self.n as int) as u64;
            }
        }
    }

    /// Returns true if there is a vertex with number u and false otherwise.
    /// This is basically a test if u < n (with n the order of the graph).
    fn is_vertex(&self, u: u64) -> bool {
        u < self.n
    }

    /// Checks whether the vertices i and j are adjacent.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    /// }
    /// assert!(!g.is_edge(10,0));
    /// ```
    fn is_edge(&self, u: u64, w: u64) -> bool {
        unsafe {
            let row = detail::graphrow(self.data.as_ptr(), u as int, self.w as int);
            detail::iselement(row, w as int)
        }
    }

    /// Adds an edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    ///     assert!(g.size() == i+1);
    /// }
    /// ```
    fn add_edge(&mut self, u: u64, w: u64) {
        unsafe {
            if !self.is_edge(u, w) {
                self.m += 1;
                detail::addoneedge(self.data.as_mut_ptr(), u as int, w as int, self.w as int);
            }
        }
    }

    /// Removes the edge between the vertices i and j.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    /// }
    /// for i in 0..10
    /// {
    ///     g.remove_edge(i,i+1);
    ///     assert!(!g.is_edge(i,i+1));
    ///     assert!(g.size() == 10-i-1);
    /// }
    /// ```
    fn remove_edge(&mut self, u: u64, w: u64) {
        unsafe {
            if self.is_edge(u, w) {
                let mut row = detail::graphrowmut(self.data.as_mut_ptr(), u as int, self.w as int);
                detail::delelement(row, w as int);
                row = detail::graphrowmut(self.data.as_mut_ptr(), w as int, self.w as int);
                detail::delelement(row, u as int);
                if u != w {
                    // loop
                    self.m -= 1;
                }
            }
        }
    }

    /// Tests whether two vertices are twins.
    /// i.e., if they have the same neighbors (they can be adjacent or not).
    /// # Examples
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(6);
    /// for x in (1..5) {
    ///     g.add_edge(0,x);
    ///     g.add_edge(5,x);
    /// }
    /// g.add_edge(0,5);
    /// assert!(g.are_twins(0,5),"basic test");
    /// g.remove_edge(0,5);
    /// assert!(g.are_twins(0,5),"not connected");
    /// g.add_edge(0,5);
    /// g.remove_edge(1,5);
    /// assert!(!g.are_twins(0,5),"neighbor removed from one");
    /// g.remove_edge(1,0);
    /// assert!(g.are_twins(0,5),"neighbor removed from both");
    /// g = GraphNauty::new(30);
    /// for i in 0..29 {
    ///     for j in i+1..30 {
    ///        g.add_edge(i,j);
    ///     }
    /// }
    /// assert!(g.are_twins(5,29),"big graph");
    /// g.remove_edge(5,29);
    /// assert!(g.are_twins(5,29),"big graph, not connected");
    /// g.remove_edge(5,28);
    /// assert!(!g.are_twins(5,29),"big graph, not twins");
    /// g = GraphNauty::new(2);
    /// assert!(!g.are_twins(1, 0), "isolated vertices");
    /// g.add_edge(0, 1);
    /// assert!(!g.are_twins(1, 0), "adjacent but no other neighbor");
    /// ```
    fn are_twins(&self, u: u64, v: u64) -> bool {
        self.compare_matrix_lines(u, v, |x, y| x == y)
    }

    /// Returns true if all the neighbors of u (v not included) are also neighbors of v.
    /// # Examples
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(6);
    /// for x in (1..5) {
    ///     g.add_edge(0,x);
    ///     g.add_edge(5,x);
    /// }
    /// g.add_edge(0,5);
    /// assert!(g.is_neighborhood_included(0,5),"basic test");
    /// g.remove_edge(0,5);
    /// assert!(g.is_neighborhood_included(0,5),"not connected");
    /// g.add_edge(0,5);
    /// g.remove_edge(1,5);
    /// assert!(!g.is_neighborhood_included(0,5),"neighbor removed from one");
    /// g.remove_edge(1,0);
    /// assert!(g.is_neighborhood_included(0,5),"neighbor removed from both");
    /// g.add_edge(1, 5);
    /// assert!(g.is_neighborhood_included(0,5),"one less neighbor for 0");
    /// g = GraphNauty::new(30);
    /// for i in 0..29 {
    ///     for j in i+1..30 {
    ///        g.add_edge(i,j);
    ///     }
    /// }
    /// assert!(g.is_neighborhood_included(5,29),"big graph");
    /// g.remove_edge(5,29);
    /// assert!(g.is_neighborhood_included(5,29),"big graph, not connected");
    /// g.remove_edge(5,28);
    /// assert!(g.is_neighborhood_included(5,29),"big graph, not twins");
    /// assert!(!g.is_neighborhood_included(29,5),"big graph, not twins");
    /// g = GraphNauty::new(3);
    /// g.add_edge(1,2);
    /// assert!(!g.is_neighborhood_included(0, 1), "isolated vertices");
    /// g.add_edge(0, 1);
    /// assert!(!g.is_neighborhood_included(1, 0), "adjacent but no other neighbor");
    /// g.add_edge(0, 2);
    /// assert!(g.is_neighborhood_included(1, 0), "one other neighbor");
    /// ```
    fn is_neighborhood_included(&self, u: u64, v: u64) -> bool {
        self.compare_matrix_lines(u, v, |x,y| (x & !y) == 0)
    }

    /// Returns the complement of the graph. i.e., the graph G' with same vertex set but where uv
    /// is in E' if and only if uv is not in E.
    /// # Examples :
    /// ```
    /// use graph::{Graph,GraphNauty};
    /// let mut g = GraphNauty::new(5);
    /// g = g.complement();
    /// for i in 0..5 {
    ///     for j in 0..5 {
    ///         if i != j {
    ///             assert!(g.is_edge(i,j));
    ///         } else {
    ///             assert!(!g.is_edge(i,j));
    ///         }
    ///     }
    /// }
    /// g = GraphNauty::new(3).complement();
    /// for i in 0..2 {
    ///     for j in (i+1)..3 {
    ///         assert!(g.is_edge(i,j));
    ///     }
    /// }
    /// ```
    fn complement(&self) -> GraphNauty {
        let mut ng = self.clone();
        let n = ng.order();
        ng.m = n * (n - 1) / 2 + n - ng.m; //There will be loops once we negate the data
        for v in ng.vertices() {
            unsafe {
                let row = detail::graphrowmut(ng.data.as_mut_ptr(), v as int, ng.w as int);
                detail::complement_set(row, ng.w, ng.n);
                ng.remove_edge(v, v);
            }
        }
        ng
    }
}

pub struct EdgeIterator<'a, G: Graph> {
    g: &'a G,
    u: u64,
    v: u64,
}

impl<'a, G: Graph> EdgeIterator<'a, G> {
    fn increment(&mut self) {
        self.u += 1;
        if self.u == self.g.order() {
            self.v += 1;
            self.u = self.v + 1;
        }
    }
}

impl<'a, G: Graph> std::iter::Iterator for EdgeIterator<'a, G> {
    type Item = (u64, u64);

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.g.order();
        if n > 1 {
            self.increment();
            while self.v < n - 1 && !self.g.is_edge(self.u, self.v) {
                self.increment();
            }
            if self.v < n - 1 {
                Some((self.v, self.u))
            } else {
                None
            }
        } else {
            None
        }
    }
}

//impl<'a> GraphIter for GraphNauty {
impl GraphIter for GraphNauty {
    type VertIter = std::ops::Range<u64>;

    /// Returns an iterator over the vertices of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty,GraphIter};
    /// let g = GraphNauty::new(11);
    /// let mut i = 0;
    /// for n in g.vertices()
    /// {
    ///     assert!(n == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.order());
    /// ```
    fn vertices(&self) -> Self::VertIter {
        0..self.n
    }

    //type EdgeIter = EdgeIterator<'a,Self>;
    ///// Returns an iterator over the edges of the graph.
    /////
    ///// # Examples
    /////
    ///// ```
    ///// use graph::{Graph,GraphNauty,GraphIter};
    ///// let mut g = GraphNauty::new(11);
    ///// for i in 0..10
    ///// {
    /////     g.add_edge(i,i+1);
    ///// }
    ///// let mut i = 0;
    ///// for e in g.edges()
    ///// {
    /////     assert!(e.1 == i+1 && e.0 == i);
    /////     i += 1;
    ///// }
    ///// assert!(i == g.size());
    ///// ```
    //fn edges(&'a self) -> EdgeIterator<'a,Self> {
    //EdgeIterator {
    //g: self,
    //u: 0,
    //v: 0,
    //}
    //}

    type NeighIter = SetIter;
    /// Returns an iterator over the neighbors of the vertx v in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use graph::{Graph,GraphNauty,GraphIter};
    /// let mut g = GraphNauty::new(11);
    /// let neighs = vec![2,6,8,9];
    /// for i in neighs.iter()
    /// {
    ///     g.add_edge(7,*i);
    /// }
    /// let mut i = 0;
    /// for u in g.neighbors(7)
    /// {
    ///     assert!(u == neighs[i]);
    ///     i += 1;
    /// }
    /// assert!(i == neighs.len());
    /// ```
    fn neighbors(&self, u: u64) -> Self::NeighIter {
        unsafe {
            let row = detail::graphrow(self.data.as_ptr(), u as int, self.w as int);
            SetIter::new(row, self.w)
        }
    }
}

impl GraphIso for GraphNauty {
    fn canon_fixed(&self, fixed: &[Vec<u64>]) -> (Self, Vec<u64>, Vec<u64>) {
        nauty::canon_graph_fixed(self, fixed)
    }
    fn canon(&self) -> (Self, Vec<u64>, Vec<u64>) {
        self.canon_fixed(&[])
    }
    fn orbits(&self, fixed: &[Vec<u64>]) -> Vec<u64> {
        nauty::orbits(self, fixed)
    }
}

impl fmt::Debug for GraphNauty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}

impl fmt::Display for GraphNauty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}
