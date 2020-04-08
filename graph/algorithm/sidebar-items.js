initSidebarItems({"fn":[["bfs",""],["dfs",""],["has_neighborhood_included","Tests whether every neighbor of u is a neighbor of v."],["isolate","Remove all edges containing u. # Examples: `use graph::{Graph,GraphNauty}; use graph::algorithm::isolate; let mut g = GraphNauty::new(5); for i in 0..4 {     for j in i..5 {         g.add_edge(i,j);     } } isolate(&mut g, 2); for i in 0..5 {     assert!(!g.is_edge(2,i)); } g.add_edge(2,3); isolate(&mut g, 3); for i in 0..5 {     assert!(!g.is_edge(3,i)); }`"],["isolate_transfo","Remove all edges containing u."]],"trait":[["Visitor",""]]});