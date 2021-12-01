use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::time::Duration;
use std::collections::HashMap;
use cpu_time::ProcessTime;
use graph::{Graph,GraphNauty};
use graph::invariants::avtotmat;
use graph::invariants::listmat_alain;
use graph::invariants::avtotmat_alain;
use graph::invariants::rapavmaxmat;
use graph::format::from_g6;
use graph::format::to_g6;


fn main() {
    avmat_graph(&"E@hO".to_string());

    /*let mut g = GraphNauty::new(8);
    g.add_edge(0,1);
    g.add_edge(1,2);
    g.add_edge(2,3);
    g.add_edge(3,4);
    g.add_edge(4,5);
    g.add_edge(5,6);
    g.add_edge(6,7);

    println!("{:?}",to_g6(&g));
    avmat_graph(&to_g6(&g));*/

    let mut listmat_dict = HashMap::<String,Vec<Vec<(u64,u64)>>>::new();

    /*if let Ok(lines) = read_lines("./graph2to9.g6") {
        let mut count = 0;
        for line in lines {
            if let Ok(ip) = line {
                let mut g: GraphNauty = from_g6(&ip).unwrap();

                //println!("{:?}",g);
                
                let (totmat, avmat, list) = avtotmat(&g);
                //let (totmat2, avmat2, list2) = avtotmat_alain(&mut g, &mut listmat_dict);

                //println!("{:?}", avtotmat(&g));

                //println!("{:?}\n", listmat_alain(g));

                /*println!("{} {}", totmat, avmat);
                println!("{} {}", totmat2, avmat2);
                println!("{:?}",list);
                println!("{:?}",list2);
                println!("");
                if(!(totmat == totmat2 && avmat == avmat2)){
                    println!("same");
                }*/

                /*print!("{:?}",g);
                let mut matching_string: String = "".to_string();
                for ma in list{
                    matching_string.push_str(",");
                    for e in &ma{
                        matching_string += &format!("{};{}:", e.0, e.1);
                    }
                    if(ma.len() > 0){
                        matching_string.pop();
                    }
                }
                print!("{}\n",matching_string);*/
            }
        }
    }*/

    let start = ProcessTime::now();

    /*let mut g: GraphNauty = from_g6(&"]D?O@UA?G?GOG?A?_A?GA_?@C?A?@???C?O@??CG?CA??CB?B????A?_@@????G@AA??????@W".to_string()).unwrap();
    let mut g: GraphNauty = from_g6(&"_?hW@aOGK??B?@????O?R????BG?A??@S??G?o?I??@?O?OO??????@????O???B?_??G???@G???O_???CK".to_string()).unwrap();
    //let mut g: GraphNauty = from_g6(&"EgKG".to_string()).unwrap();

    let (totmat, avmat, list) = avtotmat(&g);

    let cpu_time: Duration = start.elapsed();
    println!("Pour un plus gros graphe : Temps de calcul greedy : {:?}", cpu_time);   
    total1 += cpu_time; 

    let (totmat2, avmat2, list2) = avtotmat_alain(&mut g, &mut listmat_dict);

    let cpu_time2: Duration = start.elapsed()-cpu_time;
    println!("Pour un plus gros graphe : Temps de calcul récursif : {:?}", cpu_time2);
    total2 += cpu_time2;

    println!("{} {}", totmat, avmat);
    println!("{} {}", totmat2, avmat2);
    //println!("{:?}",list);
    //println!("{:?}",list2);
    println!("");*/

    /*let mut sigs = Vec::new();

    if let Ok(lines) = read_lines("./graph11.g6") {
        for line in lines {
            if let Ok(ip) = line {
                sigs.push(ip.trim().to_string());
            }
        }
    }

    use rayon::prelude::*;
    let start = ProcessTime::now();

    println!("sig,rapavmaxmat");
    sigs.par_iter().for_each(|x| avmat_graph(x));

    let cpu_time: Duration = start.elapsed();
    //println!("Pour une liste de plus petits graphes : Temps de calcul greedy : {:?}", cpu_time);

    /*if let Ok(lines) = read_lines("./test.csv") {
        for line in lines {
            if let Ok(ip) = line {
                let mut split = ip.split(",");
                let sig = split.next().unwrap();
                let mut matchings = Vec::new();
                for ma in split{
                    let mut matching = Vec::new();
                    let mut split2 = ma.split(":");
                    for e in split2{
                        if e != ""{
                            let mut split3 = e.split(";");
                            let add_e = (split3.next().unwrap().parse::<u64>().unwrap(),split3.next().unwrap().parse::<u64>().unwrap());
                            matching.push(add_e);
                        }
                    }
                    matchings.push(matching);
                }
                listmat_dict.insert(sig.to_string(),matchings);
            }
        }
    }

    println!("{:?}",listmat_dict.len());

    let cpu_time2: Duration = start.elapsed()-cpu_time;
    println!("Pour une liste de plus petits graphes : Chargement du csv : {:?}", cpu_time2);*/

    /*if let Ok(lines) = read_lines("./graph2to9.g6") {
        for line in lines {
            if let Ok(ip) = line {
                //println!("{:?}",listmat_dict);
                let mut g: GraphNauty = from_g6(&ip).unwrap();       
                //println!("{:?}",g);
                let (totmat2, avmat2, list2) = avtotmat_alain(&mut g, &mut listmat_dict);
                //println!("{:?}",list2);
                /*let gformat = to_g6(&g);
                if !listmat_dict.contains_key(&gformat){
                    listmat_dict.insert(gformat,list2.clone(),);
                }*/

                //println!("{:?}",listmat_dict.len());
            }
        }
    }

    let cpu_time3: Duration = start.elapsed()-cpu_time;
    println!("Pour une liste de plus petits graphes : Temps de calcul récursif : {:?}", cpu_time3);*/


    /*for (key, value) in &listmat_dict{
        print!("{}",key);
        let mut matching_string: String = "".to_string();
        for ma in value{
            matching_string.push_str(",");
            for e in ma{
                matching_string += &format!("{};{}:", e.0, e.1);
            }
            if(ma.len() > 0){
                matching_string.pop();
            }
        }
        print!("{}\n",matching_string);
    }*/*/
}

fn avmat_graph(sig: &String){
    let mut g: GraphNauty = from_g6(sig).unwrap();                
    let (totmat, avmat, list) = avtotmat(&g);
    println!("{},{:?},{:?},{:?},{:?}",to_g6(&g),totmat,avmat,list.len(),list);
    let rap = rapavmaxmat(&g);
    if(g.size() > 0){
        println!("{},{:?}",to_g6(&g),rap);
    }
    let mut size_dict = HashMap::<u64,u64>::new();
    for matching in list{
        let counter = size_dict.entry(matching.len() as u64).or_insert(0);
        *counter += 1;
    }
    println!("{:?}",size_dict);
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}
