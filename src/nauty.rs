extern crate libc;
use self::libc::{uint32_t, uint8_t};
use Graph;

extern "C" {
    fn nauty_wrapper(n: uint32_t,
                     m: uint32_t,
                     g: *const uint8_t,
                     lab: *mut uint32_t,
                     ptn: *mut uint32_t,
                     orbits: *mut uint32_t);
}

fn init_fixed(n: usize, fixed: &Vec<Vec<u32>>) -> (Vec<u32>, Vec<u32>) {
    let mut lab = vec![0; n];
    let mut ptn = vec![0; n];
    let mut cols = vec![n+1; n];
    let mut c = 0;
    for s in fixed {
        for &i in s {
            cols[i as usize] = c;
        }
        c += 1;
    }
    for i in 0..n {
        if cols[i] == n + 1 {
            cols[i] = c;
        }
    }
    let mut nfixed = Vec::with_capacity(c + 1);
    for i in 0..n {
        c = cols[i];
        while nfixed.len() <= c {
            nfixed.push(vec![]);
        }
        nfixed[c].push(i);
    }
    c = 0;
    for s in nfixed {
        for &i in s.iter().take(s.len() - 1) {
            lab[c] = i as u32;
            ptn[c] = 1;
            c += 1;
        }
        lab[c] = s[s.len() - 1] as u32;
        ptn[c] = 0;
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
/// use graph::Graph;
/// let mut g = Graph::new(5);
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
pub fn canon_graph_fixed(g: &Graph, fixed: &Vec<Vec<u32>>) -> (Graph, Vec<usize>, Vec<usize>) {
    unsafe {
        let n = g.order();
        let m = g.size();
        let mut orbits: Vec<u32> = vec![0; n];
        let (mut lab, mut ptn) = init_fixed(n, &fixed);

        nauty_wrapper(n as u32,
                      m as u32,
                      g.graph.to_bytes().as_slice().as_ptr(),
                      lab.as_mut_slice().as_mut_ptr(),
                      ptn.as_mut_slice().as_mut_ptr(),
                      orbits.as_mut_slice().as_mut_ptr());

        let mut ng = Graph::new(n);
        for i in 1..n {
            for j in 0..i {
                if g.is_edge(lab[i] as usize, lab[j] as usize) {
                    ng.add_edge(i, j);
                }
            }
        }
        (ng,
         lab.iter().map(|&x| x as usize).collect(),
         orbits.iter().map(|&x| x as usize).collect())
    }
}

/// Given a graph, returns the canonical form of the graph, the order of the vertices of g in the
/// new graph and the orbits with same format as nauty. The return values are in this order.
pub fn canon_graph(g: &Graph) -> (Graph, Vec<usize>, Vec<usize>) {
    canon_graph_fixed(g, &vec![])
}

/// Given orbits (nauty format), returns a vector with one vertex from each orbit.
fn orbits_sample(orbits: &Vec<usize>) -> Vec<usize> {
    let mut mi = 0;
    let mut r = vec![];
    for &o in orbits {
        if mi < o || (mi == o && r.len() == 0) {
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
/// use graph::Graph;
/// use graph::nauty::orbits;
/// let mut g = Graph::new(5);
/// let fixed: Vec<Vec<u32>> = vec![];
/// let orbsexp = vec![0,1,3];
/// g.add_edge(0,1);
/// g.add_edge(2,1);
/// let orbs = orbits(&g, &fixed);
/// assert!(orbs.len() == orbsexp.len());
/// for i in 0..orbs.len() {
///     assert!(orbs[i] == orbsexp[i]);
/// }
/// ```
pub fn orbits(g: &Graph, fixed: &Vec<Vec<u32>>) -> Vec<usize> {
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
