extern crate cc;

fn main() {
    cc::Build::new().file("nauty-wrapper.c").compile("foo")
}
