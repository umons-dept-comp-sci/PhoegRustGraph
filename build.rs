extern crate cc;

fn main() {
    cc::Build::new()
        .file("nauty-wrapper.c")
        .compile("nautywrapper");
    println!("cargo:rustc-link-lib=nauty");
}
