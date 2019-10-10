//! Module containg methods to call the nauty library in order to compute the canonical form or the
//! orbits of the vertices of a graph.
extern crate libc;
use GraphNauty;
use super::{int, graph};

#[allow(non_camel_case_types)]
type long = libc::c_ulonglong;

extern "C" {
    fn nauty_wrapper(n: long,
                     m: long,
                     g: *const graph,
                     lab: *mut int,
                     ptn: *mut int,
                     orbits: *mut int);
}

fn init_fixed(n: u64, fixed: &[Vec<u64>]) -> (Vec<i32>, Vec<i32>) {
    let mut lab = vec![0i32; n as usize];
    let mut ptn = vec![0i32; n as usize];
    let mut cols = vec![n+1; n as usize];
    let mut c = 0;
    for s in fixed.iter().filter(|x| !x.is_empty()) {
        for &i in s {
            cols[i as usize] = c;
        }
        c += 1;
    }
    for x in &mut cols {
        if *x == n + 1 {
            *x = c;
        }
    }
    let mut nfixed = Vec::with_capacity(c as usize + 1);
    for (i, c) in cols.iter().enumerate() {
        while nfixed.len() <= *c as usize {
            nfixed.push(vec![]);
        }
        nfixed[*c as usize].push(i);
    }
    c = 0;
    for s in nfixed {
        for &i in s.iter().take(s.len() - 1) {
            lab[c as usize] = i as i32;
            ptn[c as usize] = 1;
            c += 1;
        }
        lab[c as usize] = s[s.len() - 1] as i32;
        ptn[c as usize] = 0;
        c += 1;
    }
    (lab, ptn)
}

/// Given a graph and a set of fixed vertices, returns the canonical form of the graph, the order
/// of the vertices of g in the new graph and the orbits with same format as nauty. The return
/// values are in this order.
/// Example:
///
/// ```
/// use graph::nauty::canon_graph_fixed;
/// use graph::GraphNauty;
/// let mut g = GraphNauty::new(5);
/// let (_,_,orbits) = canon_graph_fixed(&g, &vec![vec![1]]);
/// println!("ORBITS {:?}", orbits);
/// let exp_orbits = vec![0,1,0,0,0];
/// assert!(orbits.len() == exp_orbits.len());
/// for i in 0..orbits.len() {
///     assert!(orbits[i] == exp_orbits[i]);
/// }
/// g.add_edge(1,0);
/// g.add_edge(2,0);
/// let (_,_,orbits) = canon_graph_fixed(&g, &vec![vec![1]]);
/// println!("ORBITS {:?}", orbits);
/// let exp_orbits = vec![0,1,2,3,3];
/// assert!(orbits.len() == exp_orbits.len());
/// for i in 0..orbits.len() {
///     assert!(orbits[i] == exp_orbits[i]);
/// }
/// g.add_edge(1,2);
/// g.add_edge(1,3);
/// g.add_edge(2,4);
/// g.add_edge(3,4);
/// let (_,_,orbits) = canon_graph_fixed(&g, &vec![vec![1,2]]);
/// println!("ORBITS {:?}", orbits);
/// let exp_orbits = vec![0,1,1,3,3];
/// assert!(orbits.len() == exp_orbits.len());
/// for i in 0..orbits.len() {
///     assert!(orbits[i] == exp_orbits[i]);
/// }
/// ```
pub fn canon_graph_fixed(g: &GraphNauty, fixed: &[Vec<u64>]) -> (GraphNauty, Vec<u64>, Vec<u64>) {
    unsafe {
        let n = g.order();
        let m = g.w;
        let mut orbits = vec![0i32; n as usize];
        let (mut lab, mut ptn) = init_fixed(n, &fixed);

        nauty_wrapper(n,
                      m,
                      g.data.as_ptr(),
                      lab.as_mut_slice().as_mut_ptr(),
                      ptn.as_mut_slice().as_mut_ptr(),
                      orbits.as_mut_slice().as_mut_ptr());

        let mut ng = GraphNauty::new(n);
        for i in 1..n {
            for j in 0..i {
                if g.is_edge(lab[i as usize] as u64, lab[j as usize] as u64) {
                    ng.add_edge(i, j);
                }
            }
        }
        let lab = lab.drain(..).map(|x| x as u64).collect();
        let orbits = orbits.drain(..).map(|x| x as u64).collect();
        (ng, lab, orbits)
    }
}

/// Given a graph, returns the canonical form of the graph, the order of the vertices of g in the
/// new graph and the orbits with same format as nauty. The return values are in this order.
pub fn canon_graph(g: &GraphNauty) -> (GraphNauty, Vec<u64>, Vec<u64>) {
    canon_graph_fixed(g, &[])
}

/// Given orbits (nauty format), returns a vector with one vertex from each orbit.
fn orbits_sample(orbits: &[u64]) -> Vec<u64> {
    let mut mi = 0;
    let mut r = vec![];
    for &o in orbits {
        if mi < o || (mi == o && r.is_empty()) {
            r.push(o);
            mi = o;
        }
    }
    r
}

/// Returns a list containing one vertex per orbit.
/// Example:
///
/// ```
/// use graph::GraphNauty;
/// use graph::nauty::orbits;
/// let mut g = GraphNauty::new(5);
/// let fixed: Vec<Vec<u64>> = vec![];
/// let orbsexp = vec![0,1,3];
/// g.add_edge(0,1);
/// g.add_edge(2,1);
/// let orbs = orbits(&g, &fixed);
/// assert!(orbs.len() == orbsexp.len());
/// for i in 0..orbs.len() {
///     assert!(orbs[i] == orbsexp[i]);
/// }
/// ```
pub fn orbits(g: &GraphNauty, fixed: &[Vec<u64>]) -> Vec<u64> {
    let (_, _, orbits) = canon_graph_fixed(g, fixed);
    orbits_sample(&orbits)
}

#[test]
fn test_orbits_sample() {
    let orbits = vec![0, 1, 2, 3, 3];
    let expected = vec![0, 1, 2, 3];
    let res = orbits_sample(&orbits);
    assert!(res.len() == expected.len());
    for i in 0..res.len() {
        assert!(expected[i] == res[i]);
    }

    let orbits = vec![0, 1, 1, 3, 3];
    let expected = vec![0, 1, 3];
    let res = orbits_sample(&orbits);
    assert!(res.len() == expected.len());
    for i in 0..res.len() {
        assert!(expected[i] == res[i]);
    }
}
