//! Module containing graph transformations.
//! Each transformation uses the orbits of the homomorphism group to filter out symmetries.
use std::collections::HashMap;
use GraphNauty;
use GraphIso;
use Graph;
use algorithm::{has_neighborhood_included,isolate_transfo};
use transfo_result::GraphTransformation;

transformation! (
    "Adds an edge.",
    add_edge,
    for g,
    let a,
    b (after a and not adj a)
    apply
    add(a,b);
);

transformation! (
    "Removes a vertex.",
    remove_vertex,
    for g,
    let a
    apply
    remove(a);
);

transformation!(
    "Removes an edge.",
    remove_edge,
    for g,
    let a,
    b sym a (after a and adj a)
    apply
    remove(a,b);
);

transformation!(
    "Given three distinct vertices a, b and c such that a and b are adjacent and c is not adjacent
to a, a rotation on a, b and c consists in removing the edge ab and adding the edge ac.
<pre>
     c        c
       ->   /
a -- b    a   b
</pre>",
    rotation,
    for g,
    let a,
    b (diff a and adj a),
    c (diff a and diff b and not adj a)
    apply
    remove(a,b);
    add(a,c);
);

transformation!(
    "A slide is similar to a rotation except that the vertices b and c must be adjacent. This
transformation does not disconnect the graph.
<pre>
     c        c
     | ->   / |
a -- b    a   b
</pre>",
    slide,
    for g,
    let a,
    b (diff a and adj a),
    c (diff a and diff b and not adj a and adj b)
    apply
    remove(a,b);
    add(a,c);
);

transformation! (
    "Given four distinct vertices a, b, c and d such that a is adjacent to b and c is not adjacent
to d, this transofrmation removes the edge ab and adds the edge cd.
<pre>
 a -- b    a    b
        ->
 c    d    c -- d
</pre>",
    move_distinct,
    for g,
    let a,
    b sym a (after a and adj a),
    c (diff a and diff b),
    d sym c (diff a and diff b and after c and not adj c)
    apply
    remove(a,b);
    add(c,d);
);

transformation! (
    "Given two distinct edges ab and cd (with distinct extremities) such that there is no edge ac
and bd, removes ab and cd and adds ac and bd.
<pre>
 a -- b    a    b
        -> |    |
 c -- d    c    d
</pre>",
    two_opt,
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
);

transformation!(
    "Given three vertices a, b and c with a adjacent to b and neither a or b adjacent to c, a detour
removes the edge ab and adds the edges ac and cb.
<pre>
     b         b
  /    ->      |
a    c    a -- c
</pre>",
    detour,
    for g,
    let a,
    b sym a (after a and adj a),
    c (diff a and diff b and not adj a and not adj b)
    apply
    remove(a,b);
    add(a,c);
    add(c,b);
);

transformation! (
    "Given three vertices a, b and c with a not adjacent to b and both a and b adjacent to c, a
shortcut removes the edges ac and cb and adds the edge ab.
<pre>
     b         b
     | ->   /
a -- c    a    c
</pre>",
    shortcut,
    for g,
    let a,
    b sym a (after a and not adj a),
    c (diff a and diff b and adj a and adj b)
    apply
    remove(a,c);
    remove(c,b);
    add(a,b);
);

transformation! (
    "Given two twin vertices (i.e., with exactly the same neighbors and optionally adjacent),
    removes the edge between them.",
    disco_twins,
    for g,
    let a,
    b (after a and adj a and twin a),
    apply
    remove(a,b);
);

transformation! (
    "Given two twin vertices, isolate one of them (i.e., removes all its edges).",
    isolate_twin,
    for g,
    let a,
    some b (after a and twin a),
    apply
    isolate(a);
);

transformation! (
    "Given two vertices u and v such that every neighbor of u is a neighbor of v, isolates u (i.e.,
removes all its edges).",
    isolate_incl,
    for g,
    let a,
    some b (diff a and incl a)
    apply
    isolate(a);
);

#[cfg(test)]
mod tests {
    use super::GraphTransformation;
    use GraphNauty;
    use format::{from_g6, to_g6};

    fn test_transfo<F>(sig: &str, trsf: F, expected: &mut Vec<&str>)
        where F: Fn(&GraphNauty) -> Vec<GraphTransformation>
    {
        let g: GraphNauty = from_g6(&String::from(sig)).unwrap();
        let mut r: Vec<GraphTransformation> = trsf(&g);
        for rg in r.iter_mut() {
            rg.canon();
        }
        assert_eq!(r.len(), expected.len());
        for rg in r.iter_mut() {
            let s = to_g6(&rg.final_graph());
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
    fn test_remove_vertex() {
        let mut expected = vec!["C^","CB","CN","CF"];
        test_transfo("DB{", super::remove_vertex, &mut expected);
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

    #[test]
    fn test_disco_twins() {
        let mut expected = vec!["E?~w","E@~o"];
        test_transfo("E@~w", super::disco_twins, &mut expected);
    }

    #[test]
    fn test_isolate_twin() {
        let mut expected = vec!["E?Dg","E@LW"];
        test_transfo("EC\\w", super::isolate_twin, &mut expected);
    }

    #[test]
    fn test_isolate_incl() {
        let mut expected = vec!["G?CHIk","G?@Hh{","G@GQW{","G@GQY{"];
        test_transfo("G@IIi{", super::isolate_incl, &mut expected);
        expected = vec![];
        test_transfo("E???", super::isolate_incl, &mut expected);
    }
}
