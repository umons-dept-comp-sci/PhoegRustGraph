use Graph;
use nauty::orbits;

pub fn add_edge(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(1);
    for i in orbits(&g, &fixed) {
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed)
            .iter()
            .filter(|&x| *x > i && !g.is_edge(*x, i)) {
            let mut ng = g.clone();
            ng.add_edge(i, j);
            res.push(ng);
        }
        fixed.pop();
    }
    res
}

pub fn remove_edge(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(1);
    for i in orbits(&g, &fixed) {
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed)
            .iter()
            .filter(|&x| *x > i && g.is_edge(*x, i)) {
            let mut ng = g.clone();
            ng.remove_edge(i, j);
            res.push(ng);
        }
        fixed.pop();
    }
    res
}

pub fn rotation(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(2);
    for i in orbits(&g, &fixed) {
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed)
            .iter()
            .filter(|&x| *x != i && g.is_edge(*x, i)) {
            fixed.push(vec![j as u32]);
            for &k in orbits(&g, &fixed)
                .iter()
                .filter(|&x| *x != j && *x != i && !g.is_edge(*x, i)) {
                let mut ng = g.clone();
                ng.remove_edge(i, j);
                ng.add_edge(i, k);
                res.push(ng);
            }
            fixed.pop();
        }
        fixed.pop();
    }
    res
}

// TODO write tests
pub fn slide(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(2);
    for i in orbits(&g, &fixed) {
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed)
            .iter()
            .filter(|&x| *x != i && g.is_edge(*x, i)) {
            fixed.push(vec![j as u32]);
            for &k in orbits(&g, &fixed)
                .iter()
                .filter(|&x| *x != j && *x != i && !g.is_edge(*x, i) && g.is_edge(*x, j)) {
                let mut ng = g.clone();
                ng.remove_edge(i, j);
                ng.add_edge(i, k);
                res.push(ng);
            }
            fixed.pop();
        }
        fixed.pop();
    }
    res
}

pub fn move_distinct(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(2);
    let mut fixed2 = Vec::with_capacity(1);
    for i in orbits(&g, &fixed) {
        println!("i {} {:?}", i, orbits(&g, &fixed));
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed).iter().filter(|&x| *x > i && g.is_edge(*x, i)) {
            println!("j {} {:?}", j, orbits(&g, &fixed));
            fixed[0].push(j as u32);
            for &k in orbits(&g, &fixed2).iter().filter(|&x| *x != i && *x != j) {
                println!("k {} {:?}", k, orbits(&g, &fixed2));
                fixed2.push(vec![k as u32]);
                for &l in orbits(&g, &fixed2)
                    .iter()
                    .filter(|&x| *x != i && *x != j && *x > k && !g.is_edge(*x, k)) {
                    let mut ng = g.clone();
                    ng.remove_edge(i, j);
                    ng.add_edge(k, l);
                    res.push(ng);
                }
                fixed2.pop();
            }
            fixed.pop();
        }
        fixed.pop();
    }
    res
}

pub fn two_opt(g: &Graph) -> Vec<Graph> {
    let mut res = vec![];
    let mut fixed = Vec::with_capacity(2);
    let mut fixed2 = Vec::with_capacity(1);
    for i in orbits(&g, &fixed) {
        println!("i {} {:?}", i, orbits(&g, &fixed));
        fixed.push(vec![i as u32]);
        for &j in orbits(&g, &fixed).iter().filter(|&x| *x > i && g.is_edge(*x, i)) {
            println!("j {} {:?}", j, orbits(&g, &fixed));
            fixed[0].push(j as u32);
            for &k in orbits(&g, &fixed2)
                .iter()
                .filter(|&x| *x != i && *x != j && !g.is_edge(*x, i)) {
                println!("k {} {:?}", k, orbits(&g, &fixed2));
                fixed2.push(vec![k as u32]);
                for &l in orbits(&g, &fixed2)
                    .iter()
                    .filter(|&x| {
                        *x != i && *x != j && *x > k && g.is_edge(*x, k) && !g.is_edge(*x, j)
                    }) {
                    let mut ng = g.clone();
                    ng.remove_edge(i, j);
                    ng.remove_edge(k, l);
                    ng.add_edge(i, k);
                    ng.add_edge(j, l);
                    res.push(ng);
                }
                fixed2.pop();
            }
            fixed.pop();
        }
        fixed.pop();
    }
    res
}

#[cfg(test)]
mod tests {
    use super::Graph;
    use format::{from_g6, to_g6};
    use nauty::canon_graph;

    fn test_transfo<F>(sig: &str, trsf: F, expected: &mut Vec<&str>)
        where F: Fn(&Graph) -> Vec<Graph>
    {
        let g = from_g6(&String::from(sig)).unwrap();
        let r: Vec<Graph> = trsf(&g).iter().map(|x| canon_graph(x).0).collect();
        eprintln!("{:?}", r);
        assert_eq!(r.len(), expected.len());
        for rg in r {
            let s = to_g6(&rg);
            assert!(expected.contains(&s.as_str()));
            let i = expected.iter()
                .enumerate()
                .skip_while(|&x| x.1 != &s)
                .next()
                .unwrap()
                .0;
            expected.remove(i);
        }
    }

    #[test]
    fn test_add_edge() {
        let mut expected = vec!["D@K", "DAK", "D?[", "D@o"];
        test_transfo("D?K", super::add_edge, &mut expected);
    }

    #[test]
    fn test_remove_edge() {
        let mut expected = vec!["DAK", "D@o"];
        test_transfo("DDW", super::remove_edge, &mut expected);
    }

    #[test]
    fn test_rotation() {
        let mut expected = vec!["DD[", "DD[", "D`[", "D`[", "DqK", "D@{", "DBw", "DBw", "DBw",
                                "DB["];
        test_transfo("DBw", super::rotation, &mut expected);
    }

    #[test]
    fn test_move_distinct() {
        let mut expected = vec!["DJk", "Dd[", "DB{"];
        test_transfo("Dd[", super::move_distinct, &mut expected);
    }
}
