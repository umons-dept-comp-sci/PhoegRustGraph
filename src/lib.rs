//! Crate using binary format to represent small graphs (order <= 11)

//#![feature(trace_macros)]

extern crate bit_vec;
extern crate libc;

pub mod format;
pub mod invariants;
pub mod errors;
pub mod nauty;
#[macro_use]
mod transfos_macros;
pub mod transfos;
pub mod subgraphs;

use std::fmt;


#[allow(non_camel_case_types)]
type set = libc::c_ulonglong;

#[allow(non_camel_case_types)]
// Type used by nauty in C
type int = libc::c_int;
#[allow(non_camel_case_types)]
type graph = set;


mod detail {
    use super::set;
    use super::int;
    use super::graph;
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
        pub fn sublabel(graph: *mut graph,
                        perm: *const int,
                        nperm: int,
                        workg: *mut graph,
                        m: int,
                        n: int);
    }
}


/// Structure to store a set of integers using binary words.
/// This structure can store all integers from 0 to a maximum value given in parameters to the
/// constructors. For example, a maximum value of 16 allows storing all integers from 0 to 15.
/// Since it uses 64 bits binary words, a maximum size of 64 allows using only one word and is thus
/// faster.
#[derive(Clone,Debug)]
pub struct Set {
    data: Vec<set>,
    maxm: u64,
    size: u64,
}

//TODO Add method to "expand" the set by interleaving it with zeroes. Use full for
//GraphTransformation.
//This can be done using magic numbers :
//http://graphics.stanford.edu/~seander/bithacks.html#InterleaveBMN
impl Set {
    fn initfill<PF>(maxelem: u64, pfunc: PF, val: set, numelem: u64) -> Set
        where PF: Fn(u64) -> set
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
        where C: Fn(&set, &set) -> set
    {
        for (i, a) in first.data.iter_mut().enumerate().take_while(|(i, _)| other.data.len() > *i) {
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

    fn complement_set(s: *mut set, len: u64, maxm: u64) {
        if len > 0 {
            let mut s = s;
            let mut maxm = maxm;
            unsafe {
                for _ in 0..(len - 1) {
                    *s = !*s;
                    maxm -= detail::wordsize() as u64;
                    s = s.add(1);
                }
                *s = !*s & detail::allmask(maxm as int);
            }
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
        Set::complement_set(self.data.as_mut_ptr(), self.data.len() as u64, self.maxm);
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
            set.add(i.into());
        }
        set
    }
}

struct SetIter {
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

/// Structure representing a undirected simple graph.
#[derive(Clone)]
pub struct Graph {
    data: Vec<graph>,
    n: u64,
    m: u64,
    w: u64,
}

impl Graph {
    /// Constructs a new graph with 0 edges and n vertices.
    pub fn new(ord: u64) -> Graph {
        unsafe {
            let words = detail::setwordsneeded(ord as int) as u64;
            let v = vec![0; (ord*words) as usize];
            Graph {
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
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for _ in 0..11
    /// {
    ///     g.add_vertex();
    /// }
    /// assert!(g.order() == 11);
    /// ```
    pub fn order(&self) -> u64 {
        self.n
    }

    /// Returns the size of the graph
    ///
    /// #Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
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
    pub fn size(&self) -> u64 {
        self.m
    }

    /// Adds a new vertex to the graph, increasing its order by one.
    /// Will return false if the graph had already an order of 11.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(0);
    /// assert!(g.order() == 0);
    /// for i in 0..11
    /// {
    ///     g.add_vertex();
    ///     assert!(g.order() == i+1);
    /// }
    /// ```
    pub fn add_vertex(&mut self) {
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
    /// let mut g = graph::Graph::new(7);
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
    pub fn remove_vertex(&mut self, i: u64) {
        if self.n > i {
            unsafe {
                let n = self.n;
                for u in 0..n {
                    if u != i {
                        self.remove_edge(u, i);
                    }
                }
                let mut workg = vec![0; (self.n*self.w) as usize];
                let perm: Vec<int> = (0..(self.n as int)).filter(|&x| x != i as int).collect();
                detail::sublabel(self.data.as_mut_ptr(),
                                 perm.as_ptr(),
                                 perm.len() as int,
                                 workg.as_mut_ptr(),
                                 self.w as int,
                                 self.n as int);
                self.n -= 1;
                self.w = detail::setwordsneeded(self.n as int) as u64;
            }
        }
    }

    /// Checks weither the vertices i and j are adjacent.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    /// }
    /// assert!(!g.is_edge(10,0));
    /// ```
    pub fn is_edge(&self, u: u64, w: u64) -> bool {
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
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    ///     assert!(g.is_edge(i,i+1));
    ///     assert!(g.size() == i+1);
    /// }
    /// ```
    pub fn add_edge(&mut self, u: u64, w: u64) {
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
    /// let mut g = graph::Graph::new(11);
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
    pub fn remove_edge(&mut self, u: u64, w: u64) {
        unsafe {
            if self.is_edge(u, w) {
                let mut row = detail::graphrowmut(self.data.as_mut_ptr(), u as int, self.w as int);
                detail::delelement(row, w as int);
                row = detail::graphrowmut(self.data.as_mut_ptr(), w as int, self.w as int);
                detail::delelement(row, u as int);
                self.m -= 1;
            }
        }
    }

    /// Returns an iterator over the vertices of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let g = graph::Graph::new(11);
    /// let mut i = 0;
    /// for n in g.vertices()
    /// {
    ///     assert!(n == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.order());
    /// ```
    pub fn vertices(&self) -> impl Iterator<Item = u64> {
        (0..self.n)
    }

    /// Returns an iterator over the edges of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
    /// for i in 0..10
    /// {
    ///     g.add_edge(i,i+1);
    /// }
    /// let mut i = 0;
    /// for e in g.edges()
    /// {
    ///     assert!(e.1 == i+1 && e.0 == i);
    ///     i += 1;
    /// }
    /// assert!(i == g.size());
    /// ```
    pub fn edges(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        unsafe {
            (0..(self.n.saturating_sub(1))).flat_map(move |x| {
                std::iter::repeat(x).zip(SetIter::with_pos(detail::graphrow(self.data.as_ptr(),
                                                                            x as int,
                                                                            self.w as int),
                                                           self.w,
                                                           x as i64))
            })
        }
    }

    /// Returns an iterator over the neighbors of the vertx v in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut g = graph::Graph::new(11);
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
    pub fn neighbors(&self, u: u64) -> impl Iterator<Item = u64> {
        unsafe {
            let row = detail::graphrow(self.data.as_ptr(), u as int, self.w as int);
            SetIter::new(row, self.w)
        }
    }
}

impl fmt::Debug for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}

impl fmt::Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format::to_g6(self))
    }
}
