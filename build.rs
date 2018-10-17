extern crate cc;

fn main() {
    println!("cargo:rerun-if-changed=nauty-wrapper.c");
    cc::Build::new()
        .file("nauty-wrapper.c")
        .compile("nautywrapper");
    println!("cargo:rustc-link-lib=nauty");
}
