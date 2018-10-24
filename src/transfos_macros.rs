macro_rules! replace_expr {
    ($_t:tt $sub:expr) => {$sub};
}
macro_rules! count
{
    ($($ts:tt)*) => {<[()]>::len(&[$(replace_expr!($ts ())),*]) as u64};
}

macro_rules! build_map {
    (@ident ($m:ident) ($a:ident ($($_r:tt)*)) ($($counts:tt)*) ($($ids:tt)*)) => {
        build_map!(@ident ($m) ($a) ($($counts)*) ($($ids)*));
    };
    (@ident ($m:ident) ($a:ident) ($($counts:tt)*) ($($ids:tt)*)) => {
        $m.insert(stringify!($a),count!($($counts)*));
        build_map!(@build ($m) ($($ids)*) -> () (@ $($counts)*));
    };
    (@ident ($m:ident) ($a:ident sym $b:ident ($($_r:tt)*)) ($($counts:tt)*) ($($ids:tt)*)) => {
        build_map!(@ident ($m) ($a sym $b) ($($counts)*) ($($ids)*));
    };
    (@ident ($m:ident) ($a:ident sym $b:ident) ($($counts:tt)*) ($($ids:tt)*)) => {
        let index = *($m.get(stringify!($b)).expect(concat!("Variable ",stringify!($b)," not yet defined when inserting ",stringify!($a))));
        $m.insert(stringify!($a),index);
        build_map!(@build ($m) ($($ids)*) -> () ($($counts)*));
    };
    (@build ($m:ident) () -> () ($($counts:tt)*)) => {};
    (@build ($m:ident) () -> ($($a:tt)+) ($($counts:tt)*)) => {
        build_map!(@ident ($m) ($($a)+) ($($counts)*) ());
    };
    (@build ($m:ident) (apply $($o_:tt)*) -> ($($a:tt)*) ($($counts:tt)*)) => {
        build_map!(@build ($m) () -> ($($a)*) ($($counts)*));
    };
    (@build ($m:ident) (, $($ids:tt)*) -> ($($a:tt)+) ($($counts:tt)*)) => {
        build_map!(@ident ($m) ($($a)+) ($($counts)*) ($($ids)*));
    };
    (@build ($m:ident) ($tok:tt $($ids:tt)*) -> ($($a:tt)*) ($($counts:tt)*)) => {
        build_map!(@build ($m) ($($ids)*) -> ($($a)* $tok) ($($counts)*));
    };
    (let $($tts:tt)*) => {
        {
            let mut m :HashMap<&str,u64> = HashMap::new();
            build_map!(@build (m) ($($tts)*) -> () ());
            m
        }
    };
}

/// Parses conditions on vertices
macro_rules! cond{
    (@translate $g:ident $x:ident (diff $b:ident)) => {
        $x != $b
    };
    (@translate $g:ident $x:ident (after $b:ident)) => {
        $x > $b
    };
    (@translate $g:ident $x:ident (adj $b:ident)) => {
        $g.is_edge($x,$b)
    };
    (@translate $g:ident $x:ident (not adj $b:ident)) => {
        !$g.is_edge($x,$b)
    };
    ($g:ident $x:ident () -> ()) => {};
    ($g:ident $x:ident () -> ($($p:tt)+)) => {
        cond!(@translate $g $x ($($p)*))
    };
    ($g:ident $x:ident (and $($r:tt)+) -> ($($p:tt)+)) => {
        cond!(@translate $g $x ($($p)*)) && cond!($g $x ($($r)*) -> ())
    };
    ($g:ident $x:ident ($tok:tt $($r:tt)*) -> ($($p:tt)*)) => {
        cond!($g $x ($($r)*) -> ($($p)* $tok))
    };
}

/// Parses weither we need conditions on a vertex
/// (vars) (vertex) (to parse) -> (parsed) (rest)
macro_rules! ifcond {
    //Nothing left to parse
    (($($v:tt)*) ($a:ident) () -> ($($b:tt)*) ($($t:tt)*)) => {
        index!(($($v)*) ($a $($b)*) ($($t)*));
    };
    //No conditions
    (($($v:tt)*) ($a:ident) (()) -> ($($b:tt)*) ($($t:tt)*)) => {
        ifcond!(($($v)*) ($a) () -> ($($b)*) ($($t)*));
    };
    //Found condition block
    (($m:ident $f:ident $res:ident $g:ident) ($a:ident) (($($p:tt)+)) -> ($($b:tt)*) ($($t:tt)*)) => {
        if cond!($g $a ($($p)*) -> ())
        {
            index!(($m $f $res $g) ($a $($b)*) ($($t)*));
        }
    };
    //Looking for condition block (could be sym constraint before the ()'s)
    (($($v:tt)*) ($a:ident) ($tok:tt $($p:tt)*) -> ($($b:tt)*) ($($t:tt)*)) => {
        ifcond!(($($v)*) ($a) ($($p)*) -> ($($b)* $tok) ($($t)*));
    };
}

/// Parses the way to add vertex to index vector
/// (alone in its orbit or same orbit as another one)
/// (vars) (constr) (rest)
macro_rules! index {
    //symmetry constraint
    (($m:ident $f:ident $($v:tt)*) ($a:ident sym $b:ident) ($($t:tt)*)) => {
        let index = *($m.get(stringify!($b))).unwrap();
        $f[index as usize].push($a);
        build_iter!(@iter ($m $f $($v)*) ($($t)*) -> ());
        $f[index as usize].pop();
    };
    //no symmetry
    (($m:ident $f:ident $($v:tt)*) ($a:ident) ($($t:tt)*)) => {
        $f.push(vec![$a]);
        build_iter!(@iter ($m $f $($v)*) ($($t)*) -> ());
        $f.pop();
    };
}

macro_rules! operation {
    (($g:ident) ()) => {};
    (($g:ident) (remove ($a:ident , $b:ident))) => {
        $g.remove_edge($a,$b)
    };
    (($g:ident) (remove ($a:ident))) => {
        $g.remove_vertex($a);
    };
    (($g:ident) (add ($a:ident , $b:ident))) => {
        $g.add_edge($a,$b);
    };
}

/// Parses the transformation list
/// (graph) (to parse) (parsed)
macro_rules! parse_transfo {
    (($g:ident) () -> ($($a:tt)*)) => {
        operation!(($g) ($($a)*));
    };
    (($g:ident) (;) -> ($($a:tt)*)) => {
        operation!(($g) ($($a)*));
    };
    (($g:ident) (; $($r:tt)+) -> ($($a:tt)*)) => {
        operation!(($g) ($($a)*));
        parse_transfo!(($g) ($($r)+) -> ());
    };
    (($g:ident) ($tok:tt $($r:tt)*) -> ($($a:tt)*)) => {
        parse_transfo!(($g) ($($r)*) -> ($($a)* $tok));
    };
}

macro_rules! build_iter {
    (@loop ($m:ident $f:ident $res:ident $g:ident) ($a:ident $($r:tt)*) ($($t:tt)*)) => {
        for &$a in &orbits(&$g, $f.as_slice()) {
            ifcond!( ($m $f $res $g) ($a) ($($r)*) -> () ($($t)*));
        }
    };
    (@iter ($($v:tt)*) () -> ($($a:tt)*)) => {};
    (@iter ($m:ident $f:ident $res:ident $g:ident) (apply $($r:tt)+) -> ()) => {
        let mut ng = TransfoResult::new(&$g);
        parse_transfo!((ng) ($($r)*) -> ());
        $res.push(ng);
    };
    (@iter ($($v:tt)*) (apply $($r:tt)+) -> ($($a:tt)+)) => {
        build_iter!(@loop ($($v)*) ($($a)*) (apply $($r)*));
    };
    (@iter ($($v:tt)*) (, $($r:tt)*) -> ($($a:tt)*)) => {
        build_iter!(@loop ($($v)*) ($($a)*) ($($r)*));
    };
    (@iter ($($v:tt)*) ($tok:tt $($r:tt)*) -> ($($a:tt)*)) => {
        build_iter!(@iter ($($v)*) ($($r)*) -> ($($a)* $tok));
    };
    (($m:ident $g:ident) let $($tts:tt)*) => {
        {
            let mut res: Vec<TransfoResult> = Vec::new();
            let mut fixed : Vec<Vec<u64>> = Vec::new();
            build_iter!(@iter ($m fixed res $g) ($($tts)*) -> ());
            res
        }
    };
    (($m:ident $g:ident) $($_:tt)*) => {
        compile_error!("Missing \"let\" before definitions of vertices.");
    }
}

macro_rules! transformation {
    (for $g:ident, $($r:tt)*) => {
        {
            #[allow(unused_variables)]
            let m = build_map!($($r)*);
            build_iter!((m $g) $($r)*)
        }
    };
    ($($_:tt)*) => {
        compile_error!("Missing \"for <graph>,\" where <graph> is the name of the graph at start of expression.");
    };
}
