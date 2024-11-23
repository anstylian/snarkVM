# ARC 81 test-drive

The purpose of this branch is to provide an example of implementing portable hashes in snarkVM.
For this demo the goal is to hash a `u8` in snarkVM and outside of hash snarkVM and produce the same hash value, using keccak256.

## snarkVM
Check the code at `example/aleo-instructions/main.aleo`

Run the code:
1. `cd example/aleo-instructions`
1. `cargo run -- run main`

The program will hash `49u8` using keccak256.

## Compare with tiny-keccak
1. `cd example/compare-tiny-keccak`
1. `cargo run`



