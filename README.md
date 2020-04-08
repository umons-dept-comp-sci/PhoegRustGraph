# PhoegRustGraph
Graph library specialized for small graphs using wrappers to the [nauty] library.

## Dependencies

The rust dependencies can be handled by Cargo.

To install nauty, either install it from your distribution repositories or
download it and compile it from source (http://pallini.di.uniroma1.it/)

Note that, to use this library in a parallel environment (cargo test is
parallel by default), nauty must be compiled with thread local storage :

```
./configure --enable-tls
make
```

## Documentation

The documentation is available [here](https://umons-dept-comp-sci.github.io/PhoegRustGraph).

[nauty]: http://pallini.di.uniroma1.it/
