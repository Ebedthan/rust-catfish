# rust-catfish
[![Crates.io](https://img.shields.io/crates/v/catfish.svg)](https://crates.io/crates/catfish)
<a href="https://github.com/Ebedthan/rust-catfish/actions?query=workflow%3A%22Continuous+Integration%22">
    <img src="https://img.shields.io/github/workflow/status/Ebedthan/rust-catfish/Continuous%20Integration?style=flat&logo=GitHub%20Actions">
</a>
[![docs.rs](https://docs.rs/catfish/badge.svg)](https://docs.rs/catfish)
[![Rust](https://img.shields.io/badge/rust-1.56.1%2B-blue.svg?maxAge=3600)](https://github.com/Ebedthan/rust-catfish)
[![License: ISC](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/Ebedthan/rust-catfish/blob/main/LICENSE)
<a href="https://codecov.io/gh/Ebedthan/rust-catfish">
    <img src="https://codecov.io/gh/Ebedthan/rust-catfish/branch/main/graph/badge.svg">
</a>
 

A library to read and write catfish files. Catfish files are directed acyclic graph files as described by
Mingfu Shao and Carl Kingsford (https://github.com/Kingsford-Group/catfish).

### Documentation

Library documentation with examples is available on [docs.rs](https://docs.rs/catfish).


### Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
catfish = "0.1"
```

Here is a simple example for reading a catfish file (like the one provided in the test directory).

```rust
use catfish::Reader;

let mut reader = catfish::Reader::from_file("path/to/file");

for result in reader.records() {
    let record = result.expect("Error parsing DAG record");
    println!("Graph header: {}\nNumber of vertices: {}\nEdges: {}", record.header(), record.num_vertices(), record.edges());
}
```

### Minimum Rust version
This crate's minimum supported `rustc` version is 1.56.1.

### License
This project is licensed under the ISC license ([LICENSE](https://github.com/Ebedthan/rust-catfish/blob/main/LICENSE) or https://opensource.org/licenses/MIT).