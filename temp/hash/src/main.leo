// The 'hash' program.
program hash.aleo {
    struct FooBar {
        foo: u8,
        bar: u16,
    }

    // The 'helloworld' main function.
    transition main() -> public u8 {
        let foobar_item: FooBar = FooBar {
            foo: 5u8,
            bar: 8u16,
        };

        return Keccak256::hash_to_u8(foobar_item);
    }

    transition foo() -> public [u8; 1] {
        return [1u8];
    }
}
