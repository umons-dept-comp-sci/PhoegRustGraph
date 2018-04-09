use std::process::Command;

fn main() {
    Command::new("make").current_dir("nauty-wrapper").output().expect("Failed to build");
    println!("cargo:rustc-link-lib=nauty");
    println!("cargo:rustc-link-search=./nauty-wrapper")
}
