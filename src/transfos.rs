use std::collections::HashMap;
use Graph;
use nauty::orbits;

pub fn add_edge(g: &Graph) -> Vec<Graph> {
    transformation! (
        for g,
        let a,
        b sym a (after a and not adj a)
        apply
        add(a,b);
        )
}

pub fn remove_edge(g: &Graph) -> Vec<Graph> {
    transformation!(
        for g,
        let a,
        b sym a (after a and adj a)
        apply
        remove(a,b);
        )
}

pub fn rotation(g: &Graph) -> Vec<Graph> {
    transformation!(
        for g,
        let a,
        b (diff a and adj a),
        c (diff a and diff b and not adj a)
        apply
        remove(a,b);
        add(a,c);
        )
}

pub fn slide(g: &Graph) -> Vec<Graph> {
    transformation!(
        for g,
        let a,
        b (diff a and adj a),
        c (diff a and diff b and not adj a and adj b)
        apply
        remove(a,b);
        add(a,c);
        )
}

pub fn move_distinct(g: &Graph) -> Vec<Graph> {
    transformation! (
        for g,
        let a,
        b sym a (after a and adj a),
        c (diff a and diff b),
        d sym c (diff a and diff b and after c and not adj c)
        apply
        remove(a,b);
        add(c,d);
        )
}

pub fn two_opt(g: &Graph) -> Vec<Graph> {
    transformation! (
        for g,
        let a,
        b sym a (after a and adj a),
        c (after a and diff b and not adj a),
        d sym c (after a and diff b and diff c and adj c and not adj b)
        apply
        remove(a,b);
        remove(c,d);
        add(a,c);
        add(b,d);
        )
}

pub fn detour(g: &Graph) -> Vec<Graph> {
    transformation!(
        for g,
        let a,
        b sym a (after a and adj a),
        c (diff a and diff b and not adj a and not adj b)
        apply
        remove(a,b);
        add(a,c);
        add(c,b);
        )
}

pub fn shortcut(g: &Graph) -> Vec<Graph> {
    transformation! (
        for g,
        let a,
        b sym a (after a and not adj a),
        c (diff a and diff b and adj a and adj b)
        apply
        remove(a,c);
        remove(c,b);
        add(a,b);
        )
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

    #[test]
    fn test_slide() {
        let mut expected = vec!["DFw", "Dd[", "DJk", "Dd[", "D`{", "DB{"];
        test_transfo("Dd[", super::slide, &mut expected);
    }

    #[test]
    fn test_two_opt() {
        let mut expected = vec!["E@hO", "E@N?", "E@hO", "E`GW", "E@hO", "E@hO"];
        test_transfo("E@hO", super::two_opt, &mut expected);
    }

    #[test]
    fn test_detour() {
        let mut expected = vec!["DR{", "DR{"];
        test_transfo("Dd[", super::detour, &mut expected);
    }

    #[test]
    fn test_shortcut() {
        let mut expected = vec!["DBw", "DB[", "D`["];
        test_transfo("Dd[", super::shortcut, &mut expected);
    }
}
