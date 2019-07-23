//! Module containing graph transformations.
//! Each transformation uses the orbits of the homomorphism group to filter out symmetries.
use std::collections::HashMap;
use Graph;
use nauty::{canon_graph, orbits};
use std::fmt;
use transfo_result::GraphTransformation;

/// Result obtained by applying a transformation to a graph.
pub struct TransfoResult {
    /// Graph to which the transformation was applied.
    start: Graph,
    /// Graph resulting from the transformation.
    end: Graph,
    /// New ordering of the vertices of `end` from the canonical form.
    order: Vec<u64>,
    /// Edges added to the graph.
    added: Graph,
    /// Edges removed from the graph.
    removed: Graph,
    /// Name of the transformation
    name: String,
}

impl TransfoResult {
    /// Creates a new `TransfoResult` with `g` as a starting point.
    /// The graph is cloned in the making.
    pub fn new(g: &Graph) -> TransfoResult {
        TransfoResult {
            start: g.clone(),
            end: g.clone(),
            order: (0..g.order()).collect(),
            added: Graph::new(g.order()),
            removed: Graph::new(g.order()),
            name: "".to_string(),
        }
    }

    /// Creates a new `TransfoResult` with `g` as a starting point and with given name.
    /// The graph is cloned in the making.
    pub fn with_name(g: &Graph, name: String) -> TransfoResult {
        let mut tr = TransfoResult::new(g);
        tr.name = name;
        tr
    }

    /// Computes the canonical form of the result as well as the order of the vertices in this
    /// form.
    pub fn canon(&mut self) {
        let (cg, ord, _) = canon_graph(&self.end);
        self.end = cg;
        self.order = ord;
    }

    /// Adds an edge.
    pub fn add_edge(&mut self, i: u64, j: u64) {
        if !self.start.is_edge(i, j) {
            self.end.add_edge(i, j);
            self.added.add_edge(i, j);
            self.removed.remove_edge(i, j);
        }
    }

    /// Removes an edge.
    pub fn remove_edge(&mut self, i: u64, j: u64) {
        if self.start.is_edge(i, j) {
            self.end.remove_edge(i, j);
            self.removed.add_edge(i, j);
            self.added.remove_edge(i, j);
        }
    }

    /// Adds a vertex.
    pub fn add_vertex(&mut self) {
        self.end.add_vertex();
        self.added.add_vertex();
    }

    /// Removes a vertex.
    pub fn remove_vertex(&mut self, i: u64) {
        self.end.remove_vertex(i);
        self.removed.remove_vertex(i);
    }

    /// Returns a reference to the result of the transformation
    pub fn get_end(&self) -> &Graph {
        &self.end
    }

    /// Sets the name of the transformation
    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }
}

impl fmt::Display for TransfoResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "\"{}\", \"{}\", \"{}\", \"{}\", \"{}\", ",
               self.name,
               self.start,
               self.end,
               self.added,
               self.removed)?;
        for i in 0..self.order.len() {
            if i > 0 {
                write!(f,";")?;
            }
            write!(f,"{}",self.order[i])?;
        }
        Ok(())
    }
}

impl fmt::Debug for TransfoResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,
               "{} : {} -> {} [added: {}, removed: {}, order: {:?}]",
               self.name,
               self.start,
               self.end,
               self.added,
               self.removed,
               self.order)
    }
}

/// Adds an edge.
pub fn add_edge(g: &Graph) -> Vec<GraphTransformation> {
    transformation! (
        "add_edge",
        for g,
        let a,
        b sym a (after a and not adj a)
        apply
        add(a,b);
        )
}

/// Removes a vertex.
pub fn remove_vertex(g: &Graph) -> Vec<GraphTransformation> {
    transformation! (
        "remove_vertex",
        for g,
        let a
        apply
        remove(a);
        )
}

/// Removes an edge.
pub fn remove_edge(g: &Graph) -> Vec<GraphTransformation> {
    transformation!(
        "remove_edge",
        for g,
        let a,
        b sym a (after a and adj a)
        apply
        remove(a,b);
        )
}

/// Given three distinct vertices a, b and c such that a and b are adjacent and c is not adjacent
/// to a, a rotation on a, b and c consists in removing the edge ab and adding the edge ac.
/// <pre>
///      c        c
///        ->   /
/// a -- b    a   b
/// </pre>
pub fn rotation(g: &Graph) -> Vec<GraphTransformation> {
    transformation!(
        "rotation",
        for g,
        let a,
        b (diff a and adj a),
        c (diff a and diff b and not adj a)
        apply
        remove(a,b);
        add(a,c);
        )
}

/// A slide is similar to a rotation except that the vertices b and c must be adjacent. This
/// transformation does not disconnect the graph.
/// <pre>
///      c        c
///      | ->   / |
/// a -- b    a   b
/// </pre>
pub fn slide(g: &Graph) -> Vec<GraphTransformation> {
    transformation!(
        "slide",
        for g,
        let a,
        b (diff a and adj a),
        c (diff a and diff b and not adj a and adj b)
        apply
        remove(a,b);
        add(a,c);
        )
}

/// Given four distinct vertices a, b, c and d such that a is adjacent to b and c is not adjacent
/// to d, this transofrmation removes the edge ab and adds the edge cd.
/// <pre>
///  a -- b    a    b
///         ->
///  c    d    c -- d
/// </pre>
pub fn move_distinct(g: &Graph) -> Vec<GraphTransformation> {
    transformation! (
        "move_distinct",
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

/// Given two distinct edges ab and cd (with distinct extremities) such that there is no edge ac
/// and bd, removes ab and cd and adds ac and bd.
/// <pre>
///  a -- b    a    b
///         -> |    |
///  c -- d    c    d
/// </pre>
pub fn two_opt(g: &Graph) -> Vec<GraphTransformation> {
    transformation! (
        "two_opt",
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

/// Given three vertices a, b and c with a adjacent to b and neither a or b adjacent to c, a detour
/// removes the edge ab and adds the edges ac and cb.
/// <pre>
///      b         b
///   /    ->      |
/// a    c    a -- c
/// </pre>
pub fn detour(g: &Graph) -> Vec<GraphTransformation> {
    transformation!(
        "detour",
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

/// Given three vertices a, b and c with a not adjacent to b and both a and b adjacent to c, a
/// shortcut removes the edges ac and cb and adds the edge ab.
/// <pre>
///      b         b
///      | ->   /
/// a -- c    a    c
/// </pre>
pub fn shortcut(g: &Graph) -> Vec<GraphTransformation> {
    transformation! (
        "shortcut",
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
    use super::GraphTransformation;
    use super::Graph;
    use format::{from_g6, to_g6};

    fn test_transfo<F>(sig: &str, trsf: F, expected: &mut Vec<&str>)
        where F: Fn(&Graph) -> Vec<GraphTransformation>
    {
        let g = from_g6(&String::from(sig)).unwrap();
        let mut r: Vec<GraphTransformation> = trsf(&g);
        for rg in r.iter_mut() {
            rg.canon();
        }
        eprintln!("{:?}", r);
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
}
