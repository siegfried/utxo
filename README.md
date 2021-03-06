# General utilities of UTxO

[![Rust](https://github.com/siegfried/utxo/actions/workflows/rust.yml/badge.svg)](https://github.com/siegfried/utxo/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/utxo)](https://crates.io/crates/utxo)

This package provides tools to ease the development of Cryptocurrencies based on UTxO model.

## UTxO Selection

This package provide a `select` function to select UTxOs, which is supposed to work on Bitcoin, Cardano, Ergo and so on. The user just need to implement the `Select` trait to use it.

Check more in the [document](https://docs.rs/utxo).


## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
   
