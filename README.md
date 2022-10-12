# PhoegRustGraph
Graph library specialized for small graphs using wrappers to the [nauty] library.

## Dependencies

The rust dependencies can be handled by Cargo.

To install nauty, either install it from your distribution repositories or
download it and compile it from source (http://pallini.di.uniroma1.it/)

Note that, to use this library in a parallel environment (cargo test is
parallel by default), nauty must be compiled with thread local storage (option `--enable-tls` of the Nauty configure script). To configure with thread local storage and install in `~/.local`:
```sh
./configure --prefix=$HOME/.local/ --includedir=$HOME/.local/include/nauty \
    --enable-tls
make install
```
If you use a user-local install, you might need to add `RUSTFLAGS="-L ~/.local/lib"` and `RUSTDOCFLAGS="$RUSTFLAGS"` to your build environment.

## Documentation

The documentation is available [here](https://umons-dept-comp-sci.github.io/PhoegRustGraph).

[nauty]: http://pallini.di.uniroma1.it/
