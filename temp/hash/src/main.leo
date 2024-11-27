// The 'hash' program.
program hash.aleo {
    struct FooBar {
        foo: u8,
        bar: u16,
    }

    // The 'helloworld' main function.
    transition main() -> group {
    /*
        let foobar_item: FooBar = FooBar {
            foo: 5u8,
            bar: 8u16,
        };
        */

        let foobar_item: u8 = 49u8;
        return Keccak256::hash_to_group(foobar_item);
    }
}
